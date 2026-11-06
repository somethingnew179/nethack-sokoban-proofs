import NetHack.Soko22Hazard87.AndIntroBlocks0135
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro34000 (p : Pattern) (ha : d125694 p = 1) (hb : d128142 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125689 q = 1) (hb : d128137 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d125689, d128137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125689, d128137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33999 q ha hb
  have h2 (q : Pattern) (ha : d125690 q = 1) (hb : d128138 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d125690, d128138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125690, d128138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d125691 q = 1) (hb : d128139 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d125691, d128139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125691, d128139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d125692 q = 1) (hb : d128140 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d125692, d128140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125692, d128140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d125693 q = 1) (hb : d128141 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d125693, d128141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125693, d128141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125694 q = 1) (hb : d128142 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d125694, d128142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125694, d128142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34001 (p : Pattern) (ha : d125700 p = 1) (hb : d128148 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d125529 q = 1) (hb : d127103 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d125529, d127103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33753 q ha hb
    | true =>
      simp only [d125529, d127103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33795 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d125569 q = 1) (hb : d127274 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d125569, d127274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125569, d127274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33841 q ha hb
  have h3 (q : Pattern) (ha : d125570 q = 1) (hb : d127275 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d125570, d127275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125570, d127275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d125610 q = 1) (hb : d127558 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d125610, d127558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125610, d127558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33894 q ha hb
  have h5 (q : Pattern) (ha : d125611 q = 1) (hb : d127559 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d125611, d127559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125611, d127559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125612 q = 1) (hb : d127560 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d125612, d127560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125612, d127560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125652 q = 1) (hb : d127851 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d125652, d127851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125652, d127851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33947 q ha hb
  have h8 (q : Pattern) (ha : d125653 q = 1) (hb : d127852 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d125653, d127852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125653, d127852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d125654 q = 1) (hb : d127853 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d125654, d127853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125654, d127853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d125655 q = 1) (hb : d127854 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d125655, d127854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d125655, d127854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d125695 q = 1) (hb : d128143 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d125695, d128143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125695, d128143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34000 q ha hb
  have h12 (q : Pattern) (ha : d125696 q = 1) (hb : d128144 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d125696, d128144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125696, d128144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d125697 q = 1) (hb : d128145 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d125697, d128145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125697, d128145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d125698 q = 1) (hb : d128146 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d125698, d128146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125698, d128146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d125699 q = 1) (hb : d128147 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d125699, d128147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d125699, d128147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d125700 q = 1) (hb : d128148 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d125700, d128148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d125700, d128148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro34002 (p : Pattern) (ha : d125706 p = 1) (hb : d128154 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125701 q = 1) (hb : d128149 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d125701, d128149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34001 q ha hb
    | true =>
      simp only [d125701, d128149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d125702 q = 1) (hb : d128150 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d125702, d128150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125702, d128150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d125703 q = 1) (hb : d128151 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d125703, d128151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125703, d128151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d125704 q = 1) (hb : d128152 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d125704, d128152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125704, d128152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125705 q = 1) (hb : d128153 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d125705, d128153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125705, d128153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125706 q = 1) (hb : d128154 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d125706, d128154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125706, d128154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34003 (p : Pattern) (ha : d125712 p = 1) (hb : d128160 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125707 q = 1) (hb : d128155 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d125707, d128155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34002 q ha hb
    | true =>
      simp only [d125707, d128155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d125708 q = 1) (hb : d128156 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d125708, d128156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125708, d128156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d125709 q = 1) (hb : d128157 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d125709, d128157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125709, d128157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d125710 q = 1) (hb : d128158 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d125710, d128158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125710, d128158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125711 q = 1) (hb : d128159 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d125711, d128159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125711, d128159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125712 q = 1) (hb : d128160 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d125712, d128160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125712, d128160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34004 (p : Pattern) (ha : d125718 p = 1) (hb : d128166 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125713 q = 1) (hb : d128161 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d125713, d128161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34003 q ha hb
    | true =>
      simp only [d125713, d128161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d125714 q = 1) (hb : d128162 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d125714, d128162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125714, d128162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d125715 q = 1) (hb : d128163 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d125715, d128163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125715, d128163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d125716 q = 1) (hb : d128164 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d125716, d128164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125716, d128164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125717 q = 1) (hb : d128165 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d125717, d128165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125717, d128165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125718 q = 1) (hb : d128166 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d125718, d128166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125718, d128166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34005 (p : Pattern) (ha : d125724 p = 1) (hb : d128172 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125719 q = 1) (hb : d128167 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d125719, d128167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34004 q ha hb
    | true =>
      simp only [d125719, d128167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d125720 q = 1) (hb : d128168 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d125720, d128168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125720, d128168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d125721 q = 1) (hb : d128169 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d125721, d128169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125721, d128169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d125722 q = 1) (hb : d128170 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d125722, d128170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125722, d128170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125723 q = 1) (hb : d128171 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d125723, d128171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125723, d128171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125724 q = 1) (hb : d128172 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d125724, d128172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125724, d128172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34006 (p : Pattern) (ha : d125730 p = 1) (hb : d128178 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125725 q = 1) (hb : d128173 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d125725, d128173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34005 q ha hb
    | true =>
      simp only [d125725, d128173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d125726 q = 1) (hb : d128174 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d125726, d128174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125726, d128174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d125727 q = 1) (hb : d128175 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d125727, d128175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125727, d128175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d125728 q = 1) (hb : d128176 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d125728, d128176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125728, d128176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125729 q = 1) (hb : d128177 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d125729, d128177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125729, d128177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125730 q = 1) (hb : d128178 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d125730, d128178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125730, d128178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34007 (p : Pattern) (ha : d125736 p = 1) (hb : d128184 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125731 q = 1) (hb : d128179 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d125731, d128179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34006 q ha hb
    | true =>
      simp only [d125731, d128179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d125732 q = 1) (hb : d128180 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d125732, d128180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125732, d128180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d125733 q = 1) (hb : d128181 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d125733, d128181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125733, d128181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d125734 q = 1) (hb : d128182 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d125734, d128182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125734, d128182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125735 q = 1) (hb : d128183 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d125735, d128183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125735, d128183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125736 q = 1) (hb : d128184 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d125736, d128184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125736, d128184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34008 (p : Pattern) (ha : d125742 p = 1) (hb : d128190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125737 q = 1) (hb : d128185 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d125737, d128185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34007 q ha hb
    | true =>
      simp only [d125737, d128185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d125738 q = 1) (hb : d128186 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d125738, d128186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125738, d128186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d125739 q = 1) (hb : d128187 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d125739, d128187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125739, d128187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d125740 q = 1) (hb : d128188 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d125740, d128188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125740, d128188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125741 q = 1) (hb : d128189 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d125741, d128189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125741, d128189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125742 q = 1) (hb : d128190 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d125742, d128190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125742, d128190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34009 (p : Pattern) (ha : d163444 p = 1) (hb : d163681 p = 1) : d163681 p = 1 := by
  have h0 (q : Pattern) (ha : d163444 q = 1) (hb : d163681 q = 1) : d163681 q = 1 := by
    exact hb
  exact h0 p ha hb
theorem andIntro34010 (p : Pattern) (ha : d14054 p = 1) (hb : d126892 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52099 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52105 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d126887 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13994 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13994, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33721 q ha hb
    | true =>
      simp only [d13994, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h5 (q : Pattern) (ha : d14050 q = 1) (hb : d126888 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14050, d126888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14050, d126888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d74076 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d14051 q = 1) (hb : d126889 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14051, d126889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14051, d126889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14052 q = 1) (hb : d126890 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14052, d126890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14052, d126890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14053 q = 1) (hb : d126891 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14053, d126891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14053, d126891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14054 q = 1) (hb : d126892 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14054, d126892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14054, d126892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro34011 (p : Pattern) (ha : d14061 p = 1) (hb : d126899 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52105 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d126887 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d13994 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13994, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33721 q ha hb
    | true =>
      simp only [d13994, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h4 (q : Pattern) (ha : d14050 q = 1) (hb : d126888 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14050, d126888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14050, d126888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d74076 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d14051 q = 1) (hb : d126889 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14051, d126889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14051, d126889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14052 q = 1) (hb : d126890 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14052, d126890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14052, d126890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14053 q = 1) (hb : d126891 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14053, d126891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14053, d126891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52148 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52152 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d126894 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d14001 q = 1) (hb : d52024 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14001, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33723 q ha hb
    | true =>
      simp only [d14001, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
  have h13 (q : Pattern) (ha : d14057 q = 1) (hb : d126895 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14057, d126895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d14057, d126895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d74083 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d14058 q = 1) (hb : d126896 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14058, d126896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d14058, d126896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d14059 q = 1) (hb : d126897 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14059, d126897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d14059, d126897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d14060 q = 1) (hb : d126898 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14060, d126898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d14060, d126898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d14061 q = 1) (hb : d126899 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14061, d126899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d14061, d126899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro34012 (p : Pattern) (ha : d126906 p = 1) (hb : d163447 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d126894 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14001 q = 1) (hb : d52024 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14001, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33723 q ha hb
    | true =>
      simp only [d14001, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
  have h3 (q : Pattern) (ha : d14057 q = 1) (hb : d126895 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14057, d126895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14057, d126895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d74083 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d14058 q = 1) (hb : d126896 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14058, d126896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14058, d126896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14059 q = 1) (hb : d126904 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14059, d126904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14059, d126904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14060 q = 1) (hb : d126905 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14060, d126905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14060, d126905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d126906 q = 1) (hb : d163447 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d126906, d163447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d126906, d163447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro34013 (p : Pattern) (ha : d126930 p = 1) (hb : d163457 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d126925 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14033 q = 1) (hb : d52062 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14033, d52062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33728 q ha hb
    | true =>
      simp only [d14033, d52062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q ha hb
  have h3 (q : Pattern) (ha : d126926 q = 1) (hb : d163453 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d126926, d163453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d126926, d163453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d74105 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d126927 q = 1) (hb : d163454 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126927, d163454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d126927, d163454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d126928 q = 1) (hb : d163455 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d126928, d163455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d126928, d163455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126929 q = 1) (hb : d163456 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d126929, d163456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d126929, d163456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d126930 q = 1) (hb : d163457 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d126930, d163457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d126930, d163457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34014 (p : Pattern) (ha : d126936 p = 1) (hb : d163463 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52093 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14062 q = 1) (hb : d126900 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14062, d126900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34010 q ha hb
    | true =>
      simp only [d14062, d126900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34011 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52164 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d14063 q = 1) (hb : d126901 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14063, d126901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14063, d126901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d126902 q = 1) (hb : d163445 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d126902, d163445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d126902, d163445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d126903 q = 1) (hb : d163446 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d126903, d163446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d126903, d163446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126907 q = 1) (hb : d163448 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d126907, d163448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d126907, d163448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34012 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52173 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d126908 q = 1) (hb : d163449 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d126908, d163449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d126908, d163449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d126909 q = 1) (hb : d163450 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d126909, d163450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d126909, d163450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d126910 q = 1) (hb : d163451 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d126910, d163451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d126910, d163451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d126911 q = 1) (hb : d163452 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d126911, d163452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126911, d163452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d126931 q = 1) (hb : d163458 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d126931, d163458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d126931, d163458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34013 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52210 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d126932 q = 1) (hb : d163459 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d126932, d163459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d126932, d163459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d126933 q = 1) (hb : d163460 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d126933, d163460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d126933, d163460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d126934 q = 1) (hb : d163461 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d126934, d163461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d126934, d163461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d126935 q = 1) (hb : d163462 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d126935, d163462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d126935, d163462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d126936 q = 1) (hb : d163463 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d126936, d163463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d126936, d163463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro34015 (p : Pattern) (ha : d126942 p = 1) (hb : d163469 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51951 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52074 q = 1) (hb : d53648 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d52074, d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52074, d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro327 q ha hb
  have h3 (q : Pattern) (ha : d52075 q = 1) (hb : d53649 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d52075, d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52075, d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d52076 q = 1) (hb : d53650 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d52076, d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52076, d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d52077 q = 1) (hb : d53651 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d52077, d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52077, d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52078 q = 1) (hb : d53652 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d52078, d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52078, d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126937 q = 1) (hb : d163464 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d126937, d163464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d126937, d163464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34014 q ha hb
  have h8 (q : Pattern) (ha : d126938 q = 1) (hb : d163465 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d126938, d163465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d126938, d163465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d126939 q = 1) (hb : d163466 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d126939, d163466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d126939, d163466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d126940 q = 1) (hb : d163467 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d126940, d163467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d126940, d163467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d126941 q = 1) (hb : d163468 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d126941, d163468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d126941, d163468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d126942 q = 1) (hb : d163469 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d126942, d163469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126942, d163469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro34016 (p : Pattern) (ha : d14230 p = 1) (hb : d127013 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d126974 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d126980 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d127002 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d14225 q = 1) (hb : d126951 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14225, d126951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33756 q ha hb
    | true =>
      simp only [d14225, d126951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33757 q ha hb
  have h5 (q : Pattern) (ha : d14226 q = 1) (hb : d127003 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14226, d127003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14226, d127003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d127009 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d14227 q = 1) (hb : d127010 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14227, d127010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14227, d127010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14228 q = 1) (hb : d127011 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14228, d127011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14228, d127011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14229 q = 1) (hb : d127012 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14229, d127012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14229, d127012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14230 q = 1) (hb : d127013 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14230, d127013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14230, d127013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro34017 (p : Pattern) (ha : d14240 p = 1) (hb : d127032 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d126974 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d126980 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d127002 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d14225 q = 1) (hb : d126951 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14225, d126951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33756 q ha hb
    | true =>
      simp only [d14225, d126951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33757 q ha hb
  have h4 (q : Pattern) (ha : d14226 q = 1) (hb : d127003 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14226, d127003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14226, d127003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d127009 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d14227 q = 1) (hb : d127010 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14227, d127010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14227, d127010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14228 q = 1) (hb : d127011 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14228, d127011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14228, d127011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14229 q = 1) (hb : d127012 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14229, d127012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14229, d127012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d127018 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d127022 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d127024 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d14235 q = 1) (hb : d126960 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14235, d126960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33759 q ha hb
    | true =>
      simp only [d14235, d126960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33760 q ha hb
  have h13 (q : Pattern) (ha : d14236 q = 1) (hb : d127025 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14236, d127025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d14236, d127025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d127028 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d14237 q = 1) (hb : d127029 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14237, d127029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d14237, d127029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d14238 q = 1) (hb : d127030 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14238, d127030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d14238, d127030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d14239 q = 1) (hb : d127031 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14239, d127031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d14239, d127031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d14240 q = 1) (hb : d127032 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14240, d127032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d14240, d127032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro34018 (p : Pattern) (ha : d127041 p = 1) (hb : d163472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d127024 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14235 q = 1) (hb : d126960 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14235, d126960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33759 q ha hb
    | true =>
      simp only [d14235, d126960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33760 q ha hb
  have h3 (q : Pattern) (ha : d14236 q = 1) (hb : d127025 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14236, d127025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14236, d127025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d127028 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d14237 q = 1) (hb : d127029 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14237, d127029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14237, d127029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14238 q = 1) (hb : d127039 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14238, d127039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14238, d127039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14239 q = 1) (hb : d127040 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14239, d127040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14239, d127040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d127041 q = 1) (hb : d163472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d127041, d163472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127041, d163472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro34019 (p : Pattern) (ha : d127090 p = 1) (hb : d163483 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d127078 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d127079 q = 1) (hb : d163478 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d127079, d163478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33791 q hb ha
    | true =>
      simp only [d127079, d163478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33766 q hb ha
  have h3 (q : Pattern) (ha : d127080 q = 1) (hb : d163479 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d127080, d163479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127080, d163479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d127086 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d127087 q = 1) (hb : d163480 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d127087, d163480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d127087, d163480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d127088 q = 1) (hb : d163481 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d127088, d163481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127088, d163481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d127089 q = 1) (hb : d163482 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d127089, d163482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127089, d163482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d127090 q = 1) (hb : d163483 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d127090, d163483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127090, d163483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34020 (p : Pattern) (ha : d127096 p = 1) (hb : d163489 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d126968 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14241 q = 1) (hb : d127033 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14241, d127033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34016 q ha hb
    | true =>
      simp only [d14241, d127033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34017 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d127035 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d14242 q = 1) (hb : d127036 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14242, d127036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14242, d127036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d127037 q = 1) (hb : d163470 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d127037, d163470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d127037, d163470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d127038 q = 1) (hb : d163471 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d127038, d163471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127038, d163471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d127042 q = 1) (hb : d163473 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d127042, d163473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d127042, d163473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34018 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52358 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d127043 q = 1) (hb : d163474 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d127043, d163474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d127043, d163474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d127044 q = 1) (hb : d163475 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d127044, d163475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d127044, d163475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d127045 q = 1) (hb : d163476 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d127045, d163476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d127045, d163476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d127046 q = 1) (hb : d163477 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d127046, d163477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d127046, d163477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d127091 q = 1) (hb : d163484 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d127091, d163484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d127091, d163484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34019 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52414 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d127092 q = 1) (hb : d163485 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d127092, d163485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d127092, d163485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d127093 q = 1) (hb : d163486 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d127093, d163486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d127093, d163486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d127094 q = 1) (hb : d163487 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d127094, d163487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d127094, d163487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d127095 q = 1) (hb : d163488 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d127095, d163488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d127095, d163488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d127096 q = 1) (hb : d163489 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d127096, d163489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d127096, d163489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro34021 (p : Pattern) (ha : d127102 p = 1) (hb : d163495 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127097 q = 1) (hb : d163490 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d127097, d163490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127097, d163490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34020 q ha hb
  have h2 (q : Pattern) (ha : d127098 q = 1) (hb : d163491 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d127098, d163491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127098, d163491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127099 q = 1) (hb : d163492 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d127099, d163492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127099, d163492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d127100 q = 1) (hb : d163493 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d127100, d163493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127100, d163493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d127101 q = 1) (hb : d163494 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d127101, d163494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127101, d163494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d127102 q = 1) (hb : d163495 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d127102, d163495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127102, d163495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34022 (p : Pattern) (ha : d14497 p = 1) (hb : d127179 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d127140 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d127146 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d127168 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d14492 q = 1) (hb : d127117 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14492, d127117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33800 q ha hb
    | true =>
      simp only [d14492, d127117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33801 q ha hb
  have h5 (q : Pattern) (ha : d14493 q = 1) (hb : d127169 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14493, d127169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14493, d127169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d127175 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d14494 q = 1) (hb : d127176 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14494, d127176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14494, d127176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14495 q = 1) (hb : d127177 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14495, d127177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14495, d127177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14496 q = 1) (hb : d127178 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14496, d127178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14496, d127178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14497 q = 1) (hb : d127179 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14497, d127179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14497, d127179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro34023 (p : Pattern) (ha : d14507 p = 1) (hb : d127198 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d127140 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d127146 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d127168 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d14492 q = 1) (hb : d127117 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14492, d127117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33800 q ha hb
    | true =>
      simp only [d14492, d127117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33801 q ha hb
  have h4 (q : Pattern) (ha : d14493 q = 1) (hb : d127169 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14493, d127169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14493, d127169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d127175 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d14494 q = 1) (hb : d127176 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14494, d127176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14494, d127176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14495 q = 1) (hb : d127177 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14495, d127177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14495, d127177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14496 q = 1) (hb : d127178 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14496, d127178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14496, d127178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d127184 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d127188 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d127190 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d14502 q = 1) (hb : d127126 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14502, d127126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33803 q ha hb
    | true =>
      simp only [d14502, d127126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33804 q ha hb
  have h13 (q : Pattern) (ha : d14503 q = 1) (hb : d127191 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14503, d127191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d14503, d127191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d127194 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d14504 q = 1) (hb : d127195 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14504, d127195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d14504, d127195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d14505 q = 1) (hb : d127196 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14505, d127196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d14505, d127196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d14506 q = 1) (hb : d127197 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14506, d127197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d14506, d127197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d14507 q = 1) (hb : d127198 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14507, d127198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d14507, d127198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro34024 (p : Pattern) (ha : d127207 p = 1) (hb : d163499 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d127190 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14502 q = 1) (hb : d127126 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14502, d127126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33803 q ha hb
    | true =>
      simp only [d14502, d127126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33804 q ha hb
  have h3 (q : Pattern) (ha : d14503 q = 1) (hb : d127191 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14503, d127191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14503, d127191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d127194 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d14504 q = 1) (hb : d127195 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14504, d127195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14504, d127195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14505 q = 1) (hb : d127205 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14505, d127205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14505, d127205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14506 q = 1) (hb : d127206 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14506, d127206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14506, d127206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d127207 q = 1) (hb : d163499 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d127207, d163499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127207, d163499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro34025 (p : Pattern) (ha : d127261 p = 1) (hb : d163510 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d127249 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d127250 q = 1) (hb : d163505 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d127250, d163505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33837 q hb ha
    | true =>
      simp only [d127250, d163505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33811 q hb ha
  have h3 (q : Pattern) (ha : d127251 q = 1) (hb : d163506 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d127251, d163506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127251, d163506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d127257 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d127258 q = 1) (hb : d163507 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d127258, d163507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d127258, d163507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d127259 q = 1) (hb : d163508 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d127259, d163508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127259, d163508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d127260 q = 1) (hb : d163509 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d127260, d163509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127260, d163509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d127261 q = 1) (hb : d163510 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d127261, d163510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127261, d163510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34026 (p : Pattern) (ha : d127267 p = 1) (hb : d163516 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d127134 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14508 q = 1) (hb : d127199 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14508, d127199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34022 q ha hb
    | true =>
      simp only [d14508, d127199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34023 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d127201 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d14509 q = 1) (hb : d127202 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14509, d127202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14509, d127202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d127203 q = 1) (hb : d163497 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d127203, d163497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d127203, d163497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d127204 q = 1) (hb : d163498 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d127204, d163498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127204, d163498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d127208 q = 1) (hb : d163500 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d127208, d163500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d127208, d163500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34024 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52579 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d127209 q = 1) (hb : d163501 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d127209, d163501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d127209, d163501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d127210 q = 1) (hb : d163502 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d127210, d163502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d127210, d163502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d127211 q = 1) (hb : d163503 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d127211, d163503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d127211, d163503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d127212 q = 1) (hb : d163504 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d127212, d163504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d127212, d163504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d127262 q = 1) (hb : d163511 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d127262, d163511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d127262, d163511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34025 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52651 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d127263 q = 1) (hb : d163512 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d127263, d163512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d127263, d163512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d127264 q = 1) (hb : d163513 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d127264, d163513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d127264, d163513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d127265 q = 1) (hb : d163514 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d127265, d163514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d127265, d163514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d127266 q = 1) (hb : d163515 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d127266, d163515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d127266, d163515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d127267 q = 1) (hb : d163516 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d127267, d163516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d127267, d163516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro34027 (p : Pattern) (ha : d127273 p = 1) (hb : d163522 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127268 q = 1) (hb : d163517 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d127268, d163517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127268, d163517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34026 q ha hb
  have h2 (q : Pattern) (ha : d127269 q = 1) (hb : d163518 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d127269, d163518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127269, d163518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127270 q = 1) (hb : d163519 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d127270, d163519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127270, d163519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d127271 q = 1) (hb : d163520 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d127271, d163520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127271, d163520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d127272 q = 1) (hb : d163521 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d127272, d163521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127272, d163521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d127273 q = 1) (hb : d163522 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d127273, d163522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127273, d163522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34028 (p : Pattern) (ha : d14804 p = 1) (hb : d127395 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d127335 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d127344 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d127376 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d14799 q = 1) (hb : d127309 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14799, d127309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33846 q ha hb
    | true =>
      simp only [d14799, d127309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33847 q ha hb
  have h5 (q : Pattern) (ha : d14800 q = 1) (hb : d127377 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14800, d127377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14800, d127377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d127391 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d14801 q = 1) (hb : d127392 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14801, d127392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14801, d127392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14802 q = 1) (hb : d127393 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14802, d127393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14802, d127393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14803 q = 1) (hb : d127394 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14803, d127394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14803, d127394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14804 q = 1) (hb : d127395 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14804, d127395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14804, d127395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro34029 (p : Pattern) (ha : d14814 p = 1) (hb : d127417 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d127335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d127344 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d127376 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d14799 q = 1) (hb : d127309 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14799, d127309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33846 q ha hb
    | true =>
      simp only [d14799, d127309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33847 q ha hb
  have h4 (q : Pattern) (ha : d14800 q = 1) (hb : d127377 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14800, d127377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14800, d127377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d127391 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d14801 q = 1) (hb : d127392 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14801, d127392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14801, d127392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14802 q = 1) (hb : d127393 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14802, d127393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14802, d127393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14803 q = 1) (hb : d127394 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14803, d127394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14803, d127394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d127401 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d127406 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d127409 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d14809 q = 1) (hb : d127319 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14809, d127319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33849 q ha hb
    | true =>
      simp only [d14809, d127319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33850 q ha hb
  have h13 (q : Pattern) (ha : d14810 q = 1) (hb : d127410 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14810, d127410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d14810, d127410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d127413 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d14811 q = 1) (hb : d127414 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14811, d127414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d14811, d127414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d14812 q = 1) (hb : d127415 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14812, d127415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d14812, d127415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d14813 q = 1) (hb : d127416 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14813, d127416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d14813, d127416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d14814 q = 1) (hb : d127417 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14814, d127417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d14814, d127417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro34030 (p : Pattern) (ha : d127442 p = 1) (hb : d163527 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d127409 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14809 q = 1) (hb : d127319 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14809, d127319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33849 q ha hb
    | true =>
      simp only [d14809, d127319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33850 q ha hb
  have h3 (q : Pattern) (ha : d14810 q = 1) (hb : d127410 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14810, d127410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14810, d127410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d127413 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d14811 q = 1) (hb : d127414 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14811, d127414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14811, d127414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14812 q = 1) (hb : d127440 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14812, d127440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14812, d127440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14813 q = 1) (hb : d127441 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14813, d127441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14813, d127441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d127442 q = 1) (hb : d163527 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d127442, d163527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127442, d163527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro34031 (p : Pattern) (ha : d127508 p = 1) (hb : d163534 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15016 q = 1) (hb : d127474 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15016, d127474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33883 q ha hb
    | true =>
      simp only [d15016, d127474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33857 q ha hb
  have h2 (q : Pattern) (ha : d15017 q = 1) (hb : d127475 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15017, d127475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15017, d127475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15018 q = 1) (hb : d127476 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15018, d127476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15018, d127476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15025 q = 1) (hb : d127477 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15025, d127477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33857 q ha hb
    | true =>
      simp only [d15025, d127477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33885 q ha hb
  have h5 (q : Pattern) (ha : d15026 q = 1) (hb : d127478 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15026, d127478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15026, d127478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15027 q = 1) (hb : d127479 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15027, d127479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15027, d127479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15028 q = 1) (hb : d127480 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15028, d127480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15028, d127480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15043 q = 1) (hb : d127494 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15043, d127494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33857 q ha hb
    | true =>
      simp only [d15043, d127494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33858 q ha hb
  have h9 (q : Pattern) (ha : d15044 q = 1) (hb : d127495 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15044, d127495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15044, d127495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15045 q = 1) (hb : d127496 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15045, d127496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15045, d127496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15046 q = 1) (hb : d127497 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15046, d127497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15046, d127497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d127507 q = 1) (hb : d163533 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d127507, d163533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d127507, d163533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d127508 q = 1) (hb : d163534 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d127508, d163534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d127508, d163534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro34032 (p : Pattern) (ha : d127514 p = 1) (hb : d163540 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127509 q = 1) (hb : d163535 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d127509, d163535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34031 q ha hb
    | true =>
      simp only [d127509, d163535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d127510 q = 1) (hb : d163536 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d127510, d163536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127510, d163536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15049 q = 1) (hb : d127500 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15049, d127500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33859 q ha hb
    | true =>
      simp only [d15049, d127500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15050 q = 1) (hb : d127501 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15050, d127501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15050, d127501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d127511 q = 1) (hb : d163537 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d127511, d163537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d127511, d163537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d127512 q = 1) (hb : d163538 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d127512, d163538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d127512, d163538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d127513 q = 1) (hb : d163539 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d127513, d163539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d127513, d163539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d127514 q = 1) (hb : d163540 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d127514, d163540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d127514, d163540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro34033 (p : Pattern) (ha : d127538 p = 1) (hb : d163546 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d127506 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d127519 q = 1) (hb : d163541 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d127519, d163541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34032 q ha hb
    | true =>
      simp only [d127519, d163541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33860 q hb ha
  have h3 (q : Pattern) (ha : d127520 q = 1) (hb : d163542 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d127520, d163542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127520, d163542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d127534 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d127535 q = 1) (hb : d163543 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d127535, d163543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d127535, d163543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d127536 q = 1) (hb : d163544 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d127536, d163544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127536, d163544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d127537 q = 1) (hb : d163545 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d127537, d163545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127537, d163545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d127538 q = 1) (hb : d163546 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d127538, d163546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127538, d163546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34034 (p : Pattern) (ha : d127551 p = 1) (hb : d163552 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d127327 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14815 q = 1) (hb : d127418 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14815, d127418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34028 q ha hb
    | true =>
      simp only [d14815, d127418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34029 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d127436 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d14816 q = 1) (hb : d127437 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14816, d127437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14816, d127437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d127438 q = 1) (hb : d163525 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d127438, d163525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d127438, d163525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d127439 q = 1) (hb : d163526 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d127439, d163526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127439, d163526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d127443 q = 1) (hb : d163528 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d127443, d163528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d127443, d163528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34030 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d127445 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d127446 q = 1) (hb : d163529 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d127446, d163529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d127446, d163529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d127447 q = 1) (hb : d163530 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d127447, d163530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d127447, d163530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d127448 q = 1) (hb : d163531 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d127448, d163531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d127448, d163531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d127449 q = 1) (hb : d163532 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d127449, d163532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d127449, d163532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d127539 q = 1) (hb : d163547 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d127539, d163547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d127539, d163547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34033 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d127546 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d127547 q = 1) (hb : d163548 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d127547, d163548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d127547, d163548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d127548 q = 1) (hb : d163549 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d127548, d163549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d127548, d163549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d127549 q = 1) (hb : d163550 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d127549, d163550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d127549, d163550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d127550 q = 1) (hb : d163551 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d127550, d163551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d127550, d163551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d127551 q = 1) (hb : d163552 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d127551, d163552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d127551, d163552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro34035 (p : Pattern) (ha : d127557 p = 1) (hb : d163558 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127552 q = 1) (hb : d163553 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d127552, d163553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127552, d163553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34034 q ha hb
  have h2 (q : Pattern) (ha : d127553 q = 1) (hb : d163554 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d127553, d163554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127553, d163554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127554 q = 1) (hb : d163555 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d127554, d163555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127554, d163555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d127555 q = 1) (hb : d163556 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d127555, d163556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127555, d163556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d127556 q = 1) (hb : d163557 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d127556, d163557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127556, d163557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d127557 q = 1) (hb : d163558 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d127557, d163558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127557, d163558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34036 (p : Pattern) (ha : d15197 p = 1) (hb : d127683 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d127623 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d127632 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d127664 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d15192 q = 1) (hb : d127597 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15192, d127597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33899 q ha hb
    | true =>
      simp only [d15192, d127597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33900 q ha hb
  have h5 (q : Pattern) (ha : d15193 q = 1) (hb : d127665 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15193, d127665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15193, d127665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d127679 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d15194 q = 1) (hb : d127680 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15194, d127680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15194, d127680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15195 q = 1) (hb : d127681 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15195, d127681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15195, d127681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15196 q = 1) (hb : d127682 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15196, d127682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15196, d127682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15197 q = 1) (hb : d127683 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15197, d127683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15197, d127683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro34037 (p : Pattern) (ha : d15207 p = 1) (hb : d127705 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d127623 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d127632 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d127664 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d15192 q = 1) (hb : d127597 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15192, d127597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33899 q ha hb
    | true =>
      simp only [d15192, d127597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33900 q ha hb
  have h4 (q : Pattern) (ha : d15193 q = 1) (hb : d127665 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15193, d127665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15193, d127665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d127679 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d15194 q = 1) (hb : d127680 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15194, d127680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15194, d127680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15195 q = 1) (hb : d127681 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15195, d127681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15195, d127681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15196 q = 1) (hb : d127682 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15196, d127682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15196, d127682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d127689 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d127694 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d127697 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d15202 q = 1) (hb : d127607 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15202, d127607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33902 q ha hb
    | true =>
      simp only [d15202, d127607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33903 q ha hb
  have h13 (q : Pattern) (ha : d15203 q = 1) (hb : d127698 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15203, d127698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d15203, d127698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d127701 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d15204 q = 1) (hb : d127702 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15204, d127702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15204, d127702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d15205 q = 1) (hb : d127703 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15205, d127703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15205, d127703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d15206 q = 1) (hb : d127704 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15206, d127704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15206, d127704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d15207 q = 1) (hb : d127705 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15207, d127705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15207, d127705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro34038 (p : Pattern) (ha : d127730 p = 1) (hb : d163564 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d127697 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15202 q = 1) (hb : d127607 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15202, d127607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33902 q ha hb
    | true =>
      simp only [d15202, d127607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33903 q ha hb
  have h3 (q : Pattern) (ha : d15203 q = 1) (hb : d127698 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15203, d127698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15203, d127698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d127701 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d15204 q = 1) (hb : d127702 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15204, d127702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15204, d127702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15205 q = 1) (hb : d127728 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15205, d127728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15205, d127728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15206 q = 1) (hb : d127729 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15206, d127729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15206, d127729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d127730 q = 1) (hb : d163564 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d127730, d163564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127730, d163564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro34039 (p : Pattern) (ha : d127801 p = 1) (hb : d163571 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15409 q = 1) (hb : d127767 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15409, d127767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33936 q ha hb
    | true =>
      simp only [d15409, d127767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33910 q ha hb
  have h2 (q : Pattern) (ha : d15410 q = 1) (hb : d127768 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15410, d127768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15410, d127768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15411 q = 1) (hb : d127769 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15411, d127769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15411, d127769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15418 q = 1) (hb : d127770 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15418, d127770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33910 q ha hb
    | true =>
      simp only [d15418, d127770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33938 q ha hb
  have h5 (q : Pattern) (ha : d15419 q = 1) (hb : d127771 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15419, d127771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15419, d127771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15420 q = 1) (hb : d127772 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15420, d127772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15420, d127772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15421 q = 1) (hb : d127773 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15421, d127773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15421, d127773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15436 q = 1) (hb : d127787 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15436, d127787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33910 q ha hb
    | true =>
      simp only [d15436, d127787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33911 q ha hb
  have h9 (q : Pattern) (ha : d15437 q = 1) (hb : d127788 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15437, d127788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15437, d127788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15438 q = 1) (hb : d127789 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15438, d127789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15438, d127789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15439 q = 1) (hb : d127790 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15439, d127790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15439, d127790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d127800 q = 1) (hb : d163570 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d127800, d163570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d127800, d163570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d127801 q = 1) (hb : d163571 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d127801, d163571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d127801, d163571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro34040 (p : Pattern) (ha : d127807 p = 1) (hb : d163577 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127802 q = 1) (hb : d163572 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d127802, d163572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34039 q ha hb
    | true =>
      simp only [d127802, d163572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d127803 q = 1) (hb : d163573 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d127803, d163573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127803, d163573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15442 q = 1) (hb : d127793 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15442, d127793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33912 q ha hb
    | true =>
      simp only [d15442, d127793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15443 q = 1) (hb : d127794 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15443, d127794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15443, d127794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d127804 q = 1) (hb : d163574 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d127804, d163574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d127804, d163574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d127805 q = 1) (hb : d163575 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d127805, d163575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d127805, d163575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d127806 q = 1) (hb : d163576 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d127806, d163576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d127806, d163576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d127807 q = 1) (hb : d163577 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d127807, d163577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d127807, d163577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro34041 (p : Pattern) (ha : d127831 p = 1) (hb : d163583 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d127799 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d127812 q = 1) (hb : d163578 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d127812, d163578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34040 q ha hb
    | true =>
      simp only [d127812, d163578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33913 q hb ha
  have h3 (q : Pattern) (ha : d127813 q = 1) (hb : d163579 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d127813, d163579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127813, d163579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d127827 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d127828 q = 1) (hb : d163580 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d127828, d163580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d127828, d163580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d127829 q = 1) (hb : d163581 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d127829, d163581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127829, d163581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d127830 q = 1) (hb : d163582 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d127830, d163582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127830, d163582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d127831 q = 1) (hb : d163583 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d127831, d163583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127831, d163583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34042 (p : Pattern) (ha : d127844 p = 1) (hb : d163589 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d127615 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15208 q = 1) (hb : d127706 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15208, d127706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34036 q ha hb
    | true =>
      simp only [d15208, d127706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34037 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d127724 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d15209 q = 1) (hb : d127725 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d15209, d127725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15209, d127725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d127726 q = 1) (hb : d163562 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d127726, d163562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d127726, d163562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d127727 q = 1) (hb : d163563 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d127727, d163563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127727, d163563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d127731 q = 1) (hb : d163565 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d127731, d163565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d127731, d163565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34038 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d127733 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d127734 q = 1) (hb : d163566 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d127734, d163566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d127734, d163566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d127735 q = 1) (hb : d163567 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d127735, d163567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d127735, d163567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d127736 q = 1) (hb : d163568 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d127736, d163568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d127736, d163568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d127737 q = 1) (hb : d163569 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d127737, d163569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d127737, d163569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d127832 q = 1) (hb : d163584 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d127832, d163584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d127832, d163584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34041 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d127839 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d127840 q = 1) (hb : d163585 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d127840, d163585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d127840, d163585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d127841 q = 1) (hb : d163586 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d127841, d163586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d127841, d163586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d127842 q = 1) (hb : d163587 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d127842, d163587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d127842, d163587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d127843 q = 1) (hb : d163588 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d127843, d163588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d127843, d163588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d127844 q = 1) (hb : d163589 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d127844, d163589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d127844, d163589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro34043 (p : Pattern) (ha : d127850 p = 1) (hb : d163595 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127845 q = 1) (hb : d163590 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d127845, d163590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127845, d163590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34042 q ha hb
  have h2 (q : Pattern) (ha : d127846 q = 1) (hb : d163591 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d127846, d163591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127846, d163591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127847 q = 1) (hb : d163592 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d127847, d163592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127847, d163592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d127848 q = 1) (hb : d163593 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d127848, d163593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127848, d163593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d127849 q = 1) (hb : d163594 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d127849, d163594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127849, d163594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d127850 q = 1) (hb : d163595 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d127850, d163595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127850, d163595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34044 (p : Pattern) (ha : d15589 p = 1) (hb : d127976 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d127917 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d127926 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d127957 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d15584 q = 1) (hb : d127891 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15584, d127891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33952 q ha hb
    | true =>
      simp only [d15584, d127891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33953 q ha hb
  have h5 (q : Pattern) (ha : d15585 q = 1) (hb : d127958 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15585, d127958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15585, d127958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d127972 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d15586 q = 1) (hb : d127973 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15586, d127973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15586, d127973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15587 q = 1) (hb : d127974 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15587, d127974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15587, d127974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15588 q = 1) (hb : d127975 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15588, d127975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15588, d127975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15589 q = 1) (hb : d127976 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15589, d127976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15589, d127976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro34045 (p : Pattern) (ha : d15599 p = 1) (hb : d127998 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d127917 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d127926 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d127957 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d15584 q = 1) (hb : d127891 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15584, d127891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33952 q ha hb
    | true =>
      simp only [d15584, d127891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33953 q ha hb
  have h4 (q : Pattern) (ha : d15585 q = 1) (hb : d127958 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15585, d127958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15585, d127958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d127972 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d15586 q = 1) (hb : d127973 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15586, d127973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15586, d127973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15587 q = 1) (hb : d127974 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15587, d127974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15587, d127974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15588 q = 1) (hb : d127975 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15588, d127975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15588, d127975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d127982 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d127987 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d127990 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d15594 q = 1) (hb : d127901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15594, d127901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33955 q ha hb
    | true =>
      simp only [d15594, d127901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33956 q ha hb
  have h13 (q : Pattern) (ha : d15595 q = 1) (hb : d127991 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15595, d127991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d15595, d127991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d127994 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d15596 q = 1) (hb : d127995 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15596, d127995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15596, d127995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d15597 q = 1) (hb : d127996 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15597, d127996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15597, d127996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d15598 q = 1) (hb : d127997 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15598, d127997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15598, d127997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d15599 q = 1) (hb : d127998 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15599, d127998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15599, d127998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro34046 (p : Pattern) (ha : d128023 p = 1) (hb : d163602 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d127990 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15594 q = 1) (hb : d127901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15594, d127901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33955 q ha hb
    | true =>
      simp only [d15594, d127901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33956 q ha hb
  have h3 (q : Pattern) (ha : d15595 q = 1) (hb : d127991 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15595, d127991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15595, d127991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d127994 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d15596 q = 1) (hb : d127995 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15596, d127995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15596, d127995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15597 q = 1) (hb : d128021 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15597, d128021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15597, d128021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15598 q = 1) (hb : d128022 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15598, d128022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15598, d128022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128023 q = 1) (hb : d163602 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128023, d163602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128023, d163602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro34047 (p : Pattern) (ha : d128093 p = 1) (hb : d163609 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15787 q = 1) (hb : d128059 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15787, d128059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33989 q ha hb
    | true =>
      simp only [d15787, d128059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33963 q ha hb
  have h2 (q : Pattern) (ha : d15788 q = 1) (hb : d128060 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15788, d128060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15788, d128060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15789 q = 1) (hb : d128061 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15789, d128061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15789, d128061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15796 q = 1) (hb : d128062 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15796, d128062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33963 q ha hb
    | true =>
      simp only [d15796, d128062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33991 q ha hb
  have h5 (q : Pattern) (ha : d15797 q = 1) (hb : d128063 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15797, d128063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15797, d128063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15798 q = 1) (hb : d128064 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15798, d128064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15798, d128064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15799 q = 1) (hb : d128065 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15799, d128065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15799, d128065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15814 q = 1) (hb : d128079 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15814, d128079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33963 q ha hb
    | true =>
      simp only [d15814, d128079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33964 q ha hb
  have h9 (q : Pattern) (ha : d15815 q = 1) (hb : d128080 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15815, d128080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15815, d128080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15816 q = 1) (hb : d128081 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15816, d128081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15816, d128081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15817 q = 1) (hb : d128082 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15817, d128082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15817, d128082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d128092 q = 1) (hb : d163608 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d128092, d163608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d128092, d163608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d128093 q = 1) (hb : d163609 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d128093, d163609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d128093, d163609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro34048 (p : Pattern) (ha : d128099 p = 1) (hb : d163615 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128094 q = 1) (hb : d163610 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d128094, d163610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34047 q ha hb
    | true =>
      simp only [d128094, d163610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128095 q = 1) (hb : d163611 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d128095, d163611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128095, d163611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15820 q = 1) (hb : d128085 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15820, d128085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33965 q ha hb
    | true =>
      simp only [d15820, d128085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15821 q = 1) (hb : d128086 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15821, d128086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15821, d128086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128096 q = 1) (hb : d163612 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d128096, d163612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128096, d163612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d128097 q = 1) (hb : d163613 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d128097, d163613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128097, d163613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d128098 q = 1) (hb : d163614 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d128098, d163614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128098, d163614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d128099 q = 1) (hb : d163615 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d128099, d163615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128099, d163615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro34049 (p : Pattern) (ha : d128123 p = 1) (hb : d163621 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128091 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d128104 q = 1) (hb : d163616 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d128104, d163616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34048 q ha hb
    | true =>
      simp only [d128104, d163616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33966 q hb ha
  have h3 (q : Pattern) (ha : d128105 q = 1) (hb : d163617 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128105, d163617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128105, d163617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d128119 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d128120 q = 1) (hb : d163618 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128120, d163618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128120, d163618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d128121 q = 1) (hb : d163619 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128121, d163619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128121, d163619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128122 q = 1) (hb : d163620 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128122, d163620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128122, d163620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128123 q = 1) (hb : d163621 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128123, d163621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128123, d163621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34050 (p : Pattern) (ha : d128136 p = 1) (hb : d163627 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d127909 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15600 q = 1) (hb : d127999 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15600, d127999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34044 q ha hb
    | true =>
      simp only [d15600, d127999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34045 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d128017 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d15601 q = 1) (hb : d128018 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d15601, d128018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15601, d128018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d128019 q = 1) (hb : d163600 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128019, d163600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d128019, d163600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d128020 q = 1) (hb : d163601 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128020, d163601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128020, d163601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128024 q = 1) (hb : d163603 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128024, d163603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d128024, d163603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34046 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d128026 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d128027 q = 1) (hb : d163604 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128027, d163604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128027, d163604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d128028 q = 1) (hb : d163605 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128028, d163605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128028, d163605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d128029 q = 1) (hb : d163606 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128029, d163606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128029, d163606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d128030 q = 1) (hb : d163607 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128030, d163607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128030, d163607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128124 q = 1) (hb : d163622 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128124, d163622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d128124, d163622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34049 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d128131 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d128132 q = 1) (hb : d163623 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128132, d163623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d128132, d163623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d128133 q = 1) (hb : d163624 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128133, d163624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d128133, d163624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d128134 q = 1) (hb : d163625 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128134, d163625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d128134, d163625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d128135 q = 1) (hb : d163626 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128135, d163626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d128135, d163626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d128136 q = 1) (hb : d163627 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128136, d163627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d128136, d163627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro34051 (p : Pattern) (ha : d128142 p = 1) (hb : d163633 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128137 q = 1) (hb : d163628 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128137, d163628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128137, d163628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34050 q ha hb
  have h2 (q : Pattern) (ha : d128138 q = 1) (hb : d163629 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128138, d163629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128138, d163629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128139 q = 1) (hb : d163630 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128139, d163630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128139, d163630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128140 q = 1) (hb : d163631 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128140, d163631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128140, d163631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128141 q = 1) (hb : d163632 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128141, d163632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128141, d163632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128142 q = 1) (hb : d163633 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128142, d163633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128142, d163633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34052 (p : Pattern) (ha : d128148 p = 1) (hb : d163639 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d127103 q = 1) (hb : d163496 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d127103, d163496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34015 q ha hb
    | true =>
      simp only [d127103, d163496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34021 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d127274 q = 1) (hb : d163523 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d127274, d163523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127274, d163523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34027 q ha hb
  have h3 (q : Pattern) (ha : d127275 q = 1) (hb : d163524 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d127275, d163524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d127275, d163524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d127558 q = 1) (hb : d163559 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d127558, d163559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127558, d163559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34035 q ha hb
  have h5 (q : Pattern) (ha : d127559 q = 1) (hb : d163560 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d127559, d163560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127559, d163560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d127560 q = 1) (hb : d163561 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d127560, d163561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d127560, d163561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d127851 q = 1) (hb : d163596 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d127851, d163596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127851, d163596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34043 q ha hb
  have h8 (q : Pattern) (ha : d127852 q = 1) (hb : d163597 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d127852, d163597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127852, d163597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d127853 q = 1) (hb : d163598 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d127853, d163598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127853, d163598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d127854 q = 1) (hb : d163599 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d127854, d163599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d127854, d163599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d128143 q = 1) (hb : d163634 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d128143, d163634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128143, d163634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34051 q ha hb
  have h12 (q : Pattern) (ha : d128144 q = 1) (hb : d163635 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d128144, d163635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128144, d163635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128145 q = 1) (hb : d163636 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d128145, d163636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128145, d163636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128146 q = 1) (hb : d163637 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d128146, d163637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128146, d163637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128147 q = 1) (hb : d163638 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d128147, d163638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128147, d163638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d128148 q = 1) (hb : d163639 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d128148, d163639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d128148, d163639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro34053 (p : Pattern) (ha : d128154 p = 1) (hb : d163645 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128149 q = 1) (hb : d163640 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d128149, d163640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34052 q ha hb
    | true =>
      simp only [d128149, d163640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128150 q = 1) (hb : d163641 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d128150, d163641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128150, d163641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d128151 q = 1) (hb : d163642 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d128151, d163642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128151, d163642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128152 q = 1) (hb : d163643 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d128152, d163643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128152, d163643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128153 q = 1) (hb : d163644 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d128153, d163644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128153, d163644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128154 q = 1) (hb : d163645 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d128154, d163645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128154, d163645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro34054 (p : Pattern) (ha : d128160 p = 1) (hb : d163651 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128155 q = 1) (hb : d163646 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d128155, d163646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34053 q ha hb
    | true =>
      simp only [d128155, d163646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128156 q = 1) (hb : d163647 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d128156, d163647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128156, d163647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d128157 q = 1) (hb : d163648 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d128157, d163648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128157, d163648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128158 q = 1) (hb : d163649 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d128158, d163649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128158, d163649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128159 q = 1) (hb : d163650 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d128159, d163650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128159, d163650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128160 q = 1) (hb : d163651 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d128160, d163651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128160, d163651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro34055 (p : Pattern) (ha : d128166 p = 1) (hb : d163657 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128161 q = 1) (hb : d163652 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d128161, d163652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34054 q ha hb
    | true =>
      simp only [d128161, d163652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128162 q = 1) (hb : d163653 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d128162, d163653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128162, d163653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d128163 q = 1) (hb : d163654 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d128163, d163654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128163, d163654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128164 q = 1) (hb : d163655 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d128164, d163655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128164, d163655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128165 q = 1) (hb : d163656 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d128165, d163656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128165, d163656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128166 q = 1) (hb : d163657 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d128166, d163657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128166, d163657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro34056 (p : Pattern) (ha : d128172 p = 1) (hb : d163663 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128167 q = 1) (hb : d163658 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d128167, d163658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34055 q ha hb
    | true =>
      simp only [d128167, d163658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128168 q = 1) (hb : d163659 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d128168, d163659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128168, d163659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d128169 q = 1) (hb : d163660 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d128169, d163660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128169, d163660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128170 q = 1) (hb : d163661 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d128170, d163661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128170, d163661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128171 q = 1) (hb : d163662 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d128171, d163662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128171, d163662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128172 q = 1) (hb : d163663 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d128172, d163663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128172, d163663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro34057 (p : Pattern) (ha : d128178 p = 1) (hb : d163669 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128173 q = 1) (hb : d163664 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d128173, d163664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34056 q ha hb
    | true =>
      simp only [d128173, d163664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128174 q = 1) (hb : d163665 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d128174, d163665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128174, d163665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d128175 q = 1) (hb : d163666 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d128175, d163666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128175, d163666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128176 q = 1) (hb : d163667 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d128176, d163667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128176, d163667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128177 q = 1) (hb : d163668 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d128177, d163668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128177, d163668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128178 q = 1) (hb : d163669 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d128178, d163669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128178, d163669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro34058 (p : Pattern) (ha : d128184 p = 1) (hb : d163675 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128179 q = 1) (hb : d163670 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d128179, d163670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34057 q ha hb
    | true =>
      simp only [d128179, d163670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128180 q = 1) (hb : d163671 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d128180, d163671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128180, d163671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d128181 q = 1) (hb : d163672 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d128181, d163672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128181, d163672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128182 q = 1) (hb : d163673 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d128182, d163673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128182, d163673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128183 q = 1) (hb : d163674 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d128183, d163674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128183, d163674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128184 q = 1) (hb : d163675 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d128184, d163675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128184, d163675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro34059 (p : Pattern) (ha : d128190 p = 1) (hb : d163681 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128185 q = 1) (hb : d163676 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d128185, d163676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34058 q ha hb
    | true =>
      simp only [d128185, d163676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128186 q = 1) (hb : d163677 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d128186, d163677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128186, d163677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d128187 q = 1) (hb : d163678 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d128187, d163678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128187, d163678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128188 q = 1) (hb : d163679 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d128188, d163679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128188, d163679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128189 q = 1) (hb : d163680 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d128189, d163680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128189, d163680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128190 q = 1) (hb : d163681 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d128190, d163681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128190, d163681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro34060 (p : Pattern) (ha : d14054 p = 1) (hb : d128195 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d300 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d306 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d15979 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d13994 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d14050 q = 1) (hb : d128191 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14050, d128191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14050, d128191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d5350 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d14051 q = 1) (hb : d128192 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14051, d128192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14051, d128192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14052 q = 1) (hb : d128193 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14052, d128193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14052, d128193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14053 q = 1) (hb : d128194 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14053, d128194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14053, d128194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14054 q = 1) (hb : d128195 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14054, d128195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14054, d128195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro34061 (p : Pattern) (ha : d14061 p = 1) (hb : d128200 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d306 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d15979 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d13994 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d14050 q = 1) (hb : d128191 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14050, d128191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14050, d128191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d5350 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d14051 q = 1) (hb : d128192 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14051, d128192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14051, d128192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14052 q = 1) (hb : d128193 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14052, d128193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14052, d128193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14053 q = 1) (hb : d128194 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14053, d128194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14053, d128194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d380 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d384 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d15986 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d14001 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d14057 q = 1) (hb : d128196 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14057, d128196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d14057, d128196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d5357 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d14058 q = 1) (hb : d128197 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14058, d128197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d14058, d128197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d14059 q = 1) (hb : d128198 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14059, d128198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d14059, d128198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d14060 q = 1) (hb : d128199 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14060, d128199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d14060, d128199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d14061 q = 1) (hb : d128200 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14061, d128200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d14061, d128200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro34062 (p : Pattern) (ha : d128207 p = 1) (hb : d163447 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15986 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d14001 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d14057 q = 1) (hb : d128196 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14057, d128196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14057, d128196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d5357 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d14058 q = 1) (hb : d128197 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14058, d128197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14058, d128197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14059 q = 1) (hb : d128205 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14059, d128205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14059, d128205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14060 q = 1) (hb : d128206 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14060, d128206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14060, d128206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128207 q = 1) (hb : d163447 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128207, d163447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128207, d163447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro34063 (p : Pattern) (ha : d128217 p = 1) (hb : d163457 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16017 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d14033 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d128213 q = 1) (hb : d163453 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128213, d163453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128213, d163453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d5379 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d128214 q = 1) (hb : d163454 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128214, d163454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128214, d163454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d128215 q = 1) (hb : d163455 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128215, d163455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128215, d163455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128216 q = 1) (hb : d163456 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128216, d163456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128216, d163456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128217 q = 1) (hb : d163457 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128217, d163457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128217, d163457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34064 (p : Pattern) (ha : d128223 p = 1) (hb : d163463 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d294 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14062 q = 1) (hb : d128201 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14062, d128201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34060 q ha hb
    | true =>
      simp only [d14062, d128201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34061 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d398 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d14063 q = 1) (hb : d128202 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14063, d128202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14063, d128202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d128203 q = 1) (hb : d163445 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128203, d163445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d128203, d163445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128204 q = 1) (hb : d163446 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128204, d163446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128204, d163446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128208 q = 1) (hb : d163448 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128208, d163448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128208, d163448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34062 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d407 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d128209 q = 1) (hb : d163449 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128209, d163449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128209, d163449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d128210 q = 1) (hb : d163450 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128210, d163450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128210, d163450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d128211 q = 1) (hb : d163451 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128211, d163451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128211, d163451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d128212 q = 1) (hb : d163452 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128212, d163452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128212, d163452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128218 q = 1) (hb : d163458 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128218, d163458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128218, d163458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34063 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d463 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d128219 q = 1) (hb : d163459 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128219, d163459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d128219, d163459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d128220 q = 1) (hb : d163460 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128220, d163460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d128220, d163460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d128221 q = 1) (hb : d163461 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128221, d163461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d128221, d163461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d128222 q = 1) (hb : d163462 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128222, d163462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d128222, d163462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d128223 q = 1) (hb : d163463 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128223, d163463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d128223, d163463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro34065 (p : Pattern) (ha : d128229 p = 1) (hb : d163469 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d99 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51653 q = 1) (hb : d53648 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d51653, d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51653, d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro376 q ha hb
  have h3 (q : Pattern) (ha : d51654 q = 1) (hb : d53649 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d51654, d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51654, d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d51655 q = 1) (hb : d53650 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d51655, d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51655, d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51656 q = 1) (hb : d53651 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d51656, d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51656, d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51657 q = 1) (hb : d53652 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d51657, d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51657, d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128224 q = 1) (hb : d163464 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128224, d163464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128224, d163464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34064 q ha hb
  have h8 (q : Pattern) (ha : d128225 q = 1) (hb : d163465 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128225, d163465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128225, d163465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128226 q = 1) (hb : d163466 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128226, d163466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128226, d163466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d128227 q = 1) (hb : d163467 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128227, d163467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128227, d163467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d128228 q = 1) (hb : d163468 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128228, d163468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128228, d163468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d128229 q = 1) (hb : d163469 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128229, d163469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128229, d163469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro34066 (p : Pattern) (ha : d14230 p = 1) (hb : d128234 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16066 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d16072 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d16094 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d14225 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d14226 q = 1) (hb : d128230 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14226, d128230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14226, d128230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d16116 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d14227 q = 1) (hb : d128231 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14227, d128231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14227, d128231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14228 q = 1) (hb : d128232 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14228, d128232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14228, d128232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14229 q = 1) (hb : d128233 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14229, d128233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14229, d128233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14230 q = 1) (hb : d128234 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14230, d128234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14230, d128234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro34067 (p : Pattern) (ha : d14240 p = 1) (hb : d128239 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d16066 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16072 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d16094 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d14225 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d14226 q = 1) (hb : d128230 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14226, d128230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14226, d128230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d16116 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d14227 q = 1) (hb : d128231 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14227, d128231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14227, d128231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14228 q = 1) (hb : d128232 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14228, d128232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14228, d128232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14229 q = 1) (hb : d128233 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14229, d128233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14229, d128233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d16125 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d16129 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d16131 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d14235 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d14236 q = 1) (hb : d128235 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14236, d128235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d14236, d128235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d16137 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d14237 q = 1) (hb : d128236 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14237, d128236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d14237, d128236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d14238 q = 1) (hb : d128237 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14238, d128237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d14238, d128237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d14239 q = 1) (hb : d128238 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14239, d128238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d14239, d128238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d14240 q = 1) (hb : d128239 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14240, d128239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d14240, d128239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro34068 (p : Pattern) (ha : d128246 p = 1) (hb : d163472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16131 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d14235 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d14236 q = 1) (hb : d128235 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14236, d128235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14236, d128235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d16137 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d14237 q = 1) (hb : d128236 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14237, d128236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14237, d128236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14238 q = 1) (hb : d128244 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14238, d128244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14238, d128244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14239 q = 1) (hb : d128245 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14239, d128245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14239, d128245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128246 q = 1) (hb : d163472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128246, d163472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128246, d163472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro34069 (p : Pattern) (ha : d128256 p = 1) (hb : d163483 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16187 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d163478 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d128252 q = 1) (hb : d163479 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128252, d163479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128252, d163479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d16209 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d128253 q = 1) (hb : d163480 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128253, d163480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128253, d163480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d128254 q = 1) (hb : d163481 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128254, d163481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128254, d163481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128255 q = 1) (hb : d163482 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128255, d163482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128255, d163482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128256 q = 1) (hb : d163483 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128256, d163483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128256, d163483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34070 (p : Pattern) (ha : d128262 p = 1) (hb : d163489 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d16060 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14241 q = 1) (hb : d128240 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14241, d128240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34066 q ha hb
    | true =>
      simp only [d14241, d128240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34067 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d16144 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d14242 q = 1) (hb : d128241 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14242, d128241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14242, d128241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d128242 q = 1) (hb : d163470 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128242, d163470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d128242, d163470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128243 q = 1) (hb : d163471 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128243, d163471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128243, d163471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128247 q = 1) (hb : d163473 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128247, d163473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128247, d163473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34068 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d654 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d128248 q = 1) (hb : d163474 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128248, d163474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128248, d163474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d128249 q = 1) (hb : d163475 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128249, d163475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128249, d163475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d128250 q = 1) (hb : d163476 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128250, d163476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128250, d163476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d128251 q = 1) (hb : d163477 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128251, d163477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128251, d163477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128257 q = 1) (hb : d163484 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128257, d163484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128257, d163484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34069 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d737 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d128258 q = 1) (hb : d163485 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128258, d163485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d128258, d163485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d128259 q = 1) (hb : d163486 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128259, d163486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d128259, d163486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d128260 q = 1) (hb : d163487 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128260, d163487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d128260, d163487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d128261 q = 1) (hb : d163488 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128261, d163488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d128261, d163488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d128262 q = 1) (hb : d163489 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128262, d163489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d128262, d163489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro34071 (p : Pattern) (ha : d128268 p = 1) (hb : d163495 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128263 q = 1) (hb : d163490 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128263, d163490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128263, d163490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34070 q ha hb
  have h2 (q : Pattern) (ha : d128264 q = 1) (hb : d163491 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128264, d163491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128264, d163491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128265 q = 1) (hb : d163492 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128265, d163492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128265, d163492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128266 q = 1) (hb : d163493 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128266, d163493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128266, d163493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128267 q = 1) (hb : d163494 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128267, d163494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128267, d163494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128268 q = 1) (hb : d163495 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128268, d163495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128268, d163495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34072 (p : Pattern) (ha : d14497 p = 1) (hb : d128274 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16263 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d16269 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d16291 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d14492 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d14493 q = 1) (hb : d128270 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14493, d128270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14493, d128270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d16316 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d14494 q = 1) (hb : d128271 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14494, d128271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14494, d128271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14495 q = 1) (hb : d128272 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14495, d128272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14495, d128272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14496 q = 1) (hb : d128273 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14496, d128273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14496, d128273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14497 q = 1) (hb : d128274 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14497, d128274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14497, d128274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro34073 (p : Pattern) (ha : d14507 p = 1) (hb : d128279 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d16263 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16269 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d16291 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d14492 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d14493 q = 1) (hb : d128270 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14493, d128270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14493, d128270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d16316 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d14494 q = 1) (hb : d128271 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14494, d128271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14494, d128271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14495 q = 1) (hb : d128272 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14495, d128272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14495, d128272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14496 q = 1) (hb : d128273 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14496, d128273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14496, d128273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d16325 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d16329 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d16331 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d14502 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d14503 q = 1) (hb : d128275 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14503, d128275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d14503, d128275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d16337 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d14504 q = 1) (hb : d128276 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14504, d128276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d14504, d128276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d14505 q = 1) (hb : d128277 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14505, d128277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d14505, d128277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d14506 q = 1) (hb : d128278 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14506, d128278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d14506, d128278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d14507 q = 1) (hb : d128279 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14507, d128279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d14507, d128279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro34074 (p : Pattern) (ha : d128286 p = 1) (hb : d163499 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16331 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d14502 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d14503 q = 1) (hb : d128275 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14503, d128275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14503, d128275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d16337 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d14504 q = 1) (hb : d128276 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14504, d128276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14504, d128276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14505 q = 1) (hb : d128284 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14505, d128284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14505, d128284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14506 q = 1) (hb : d128285 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14506, d128285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14506, d128285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128286 q = 1) (hb : d163499 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128286, d163499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128286, d163499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro34075 (p : Pattern) (ha : d128296 p = 1) (hb : d163510 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16392 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d163505 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d128292 q = 1) (hb : d163506 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128292, d163506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128292, d163506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d16419 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d128293 q = 1) (hb : d163507 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128293, d163507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128293, d163507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d128294 q = 1) (hb : d163508 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128294, d163508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128294, d163508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128295 q = 1) (hb : d163509 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128295, d163509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128295, d163509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128296 q = 1) (hb : d163510 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128296, d163510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128296, d163510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34076 (p : Pattern) (ha : d128302 p = 1) (hb : d163516 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d16257 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14508 q = 1) (hb : d128280 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14508, d128280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34072 q ha hb
    | true =>
      simp only [d14508, d128280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34073 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d16344 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d14509 q = 1) (hb : d128281 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14509, d128281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14509, d128281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d128282 q = 1) (hb : d163497 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128282, d163497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d128282, d163497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128283 q = 1) (hb : d163498 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128283, d163498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128283, d163498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128287 q = 1) (hb : d163500 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128287, d163500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128287, d163500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34074 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d960 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d128288 q = 1) (hb : d163501 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128288, d163501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128288, d163501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d128289 q = 1) (hb : d163502 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128289, d163502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128289, d163502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d128290 q = 1) (hb : d163503 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128290, d163503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128290, d163503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d128291 q = 1) (hb : d163504 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128291, d163504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128291, d163504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128297 q = 1) (hb : d163511 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128297, d163511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128297, d163511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34075 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d1070 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d128298 q = 1) (hb : d163512 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128298, d163512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d128298, d163512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d128299 q = 1) (hb : d163513 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128299, d163513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d128299, d163513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d128300 q = 1) (hb : d163514 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128300, d163514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d128300, d163514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d128301 q = 1) (hb : d163515 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128301, d163515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d128301, d163515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d128302 q = 1) (hb : d163516 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128302, d163516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d128302, d163516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro34077 (p : Pattern) (ha : d128308 p = 1) (hb : d163522 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128303 q = 1) (hb : d163517 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128303, d163517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128303, d163517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34076 q ha hb
  have h2 (q : Pattern) (ha : d128304 q = 1) (hb : d163518 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128304, d163518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128304, d163518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128305 q = 1) (hb : d163519 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128305, d163519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128305, d163519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128306 q = 1) (hb : d163520 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128306, d163520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128306, d163520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128307 q = 1) (hb : d163521 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128307, d163521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128307, d163521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128308 q = 1) (hb : d163522 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128308, d163522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128308, d163522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34078 (p : Pattern) (ha : d14804 p = 1) (hb : d128315 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16497 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d16506 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d16538 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d14799 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d14800 q = 1) (hb : d128311 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14800, d128311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14800, d128311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d16587 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d14801 q = 1) (hb : d128312 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14801, d128312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14801, d128312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14802 q = 1) (hb : d128313 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14802, d128313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14802, d128313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14803 q = 1) (hb : d128314 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14803, d128314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14803, d128314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14804 q = 1) (hb : d128315 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14804, d128315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14804, d128315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro34079 (p : Pattern) (ha : d14814 p = 1) (hb : d128320 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d16497 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16506 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d16538 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d14799 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d14800 q = 1) (hb : d128311 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14800, d128311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14800, d128311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d16587 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d14801 q = 1) (hb : d128312 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14801, d128312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14801, d128312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14802 q = 1) (hb : d128313 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14802, d128313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14802, d128313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14803 q = 1) (hb : d128314 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14803, d128314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14803, d128314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d16597 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d16602 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d16605 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d14809 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d14810 q = 1) (hb : d128316 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14810, d128316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d14810, d128316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d16612 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d14811 q = 1) (hb : d128317 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14811, d128317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d14811, d128317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d14812 q = 1) (hb : d128318 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14812, d128318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d14812, d128318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d14813 q = 1) (hb : d128319 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14813, d128319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d14813, d128319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d14814 q = 1) (hb : d128320 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14814, d128320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d14814, d128320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro34080 (p : Pattern) (ha : d128327 p = 1) (hb : d163527 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16605 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d14809 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d14810 q = 1) (hb : d128316 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14810, d128316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14810, d128316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d16612 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d14811 q = 1) (hb : d128317 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14811, d128317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14811, d128317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14812 q = 1) (hb : d128325 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14812, d128325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14812, d128325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14813 q = 1) (hb : d128326 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14813, d128326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14813, d128326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128327 q = 1) (hb : d163527 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128327, d163527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128327, d163527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro34081 (p : Pattern) (ha : d128337 p = 1) (hb : d163546 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16705 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d163541 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d128333 q = 1) (hb : d163542 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128333, d163542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128333, d163542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d16756 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d128334 q = 1) (hb : d163543 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128334, d163543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128334, d163543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d128335 q = 1) (hb : d163544 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128335, d163544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128335, d163544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128336 q = 1) (hb : d163545 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128336, d163545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128336, d163545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128337 q = 1) (hb : d163546 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128337, d163546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128337, d163546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34082 (p : Pattern) (ha : d128343 p = 1) (hb : d163552 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d16489 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14815 q = 1) (hb : d128321 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14815, d128321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34078 q ha hb
    | true =>
      simp only [d14815, d128321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34079 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d16635 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d14816 q = 1) (hb : d128322 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14816, d128322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14816, d128322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d128323 q = 1) (hb : d163525 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128323, d163525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d128323, d163525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128324 q = 1) (hb : d163526 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128324, d163526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128324, d163526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128328 q = 1) (hb : d163528 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128328, d163528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128328, d163528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34080 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d16644 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d128329 q = 1) (hb : d163529 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128329, d163529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128329, d163529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d128330 q = 1) (hb : d163530 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128330, d163530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128330, d163530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d128331 q = 1) (hb : d163531 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128331, d163531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128331, d163531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d128332 q = 1) (hb : d163532 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128332, d163532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128332, d163532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128338 q = 1) (hb : d163547 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128338, d163547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128338, d163547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34081 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d16772 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d128339 q = 1) (hb : d163548 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128339, d163548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d128339, d163548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d128340 q = 1) (hb : d163549 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128340, d163549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d128340, d163549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d128341 q = 1) (hb : d163550 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128341, d163550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d128341, d163550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d128342 q = 1) (hb : d163551 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128342, d163551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d128342, d163551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d128343 q = 1) (hb : d163552 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128343, d163552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d128343, d163552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro34083 (p : Pattern) (ha : d128349 p = 1) (hb : d163558 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128344 q = 1) (hb : d163553 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128344, d163553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128344, d163553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34082 q ha hb
  have h2 (q : Pattern) (ha : d128345 q = 1) (hb : d163554 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128345, d163554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128345, d163554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128346 q = 1) (hb : d163555 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128346, d163555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128346, d163555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128347 q = 1) (hb : d163556 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128347, d163556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128347, d163556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128348 q = 1) (hb : d163557 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128348, d163557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128348, d163557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128349 q = 1) (hb : d163558 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128349, d163558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128349, d163558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34084 (p : Pattern) (ha : d15197 p = 1) (hb : d128357 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16849 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d16858 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d16890 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d15192 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d15193 q = 1) (hb : d128353 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15193, d128353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15193, d128353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d16942 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d15194 q = 1) (hb : d128354 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15194, d128354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15194, d128354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15195 q = 1) (hb : d128355 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15195, d128355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15195, d128355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15196 q = 1) (hb : d128356 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15196, d128356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15196, d128356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15197 q = 1) (hb : d128357 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15197, d128357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15197, d128357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro34085 (p : Pattern) (ha : d15207 p = 1) (hb : d128362 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d16849 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16858 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d16890 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d15192 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d15193 q = 1) (hb : d128353 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15193, d128353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15193, d128353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d16942 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d15194 q = 1) (hb : d128354 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15194, d128354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15194, d128354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15195 q = 1) (hb : d128355 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15195, d128355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15195, d128355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15196 q = 1) (hb : d128356 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15196, d128356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15196, d128356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d16952 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d16957 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d16960 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d15202 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d15203 q = 1) (hb : d128358 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15203, d128358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d15203, d128358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d16967 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d15204 q = 1) (hb : d128359 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15204, d128359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15204, d128359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d15205 q = 1) (hb : d128360 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15205, d128360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15205, d128360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d15206 q = 1) (hb : d128361 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15206, d128361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15206, d128361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d15207 q = 1) (hb : d128362 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15207, d128362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15207, d128362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro34086 (p : Pattern) (ha : d128369 p = 1) (hb : d163564 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16960 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d15202 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d15203 q = 1) (hb : d128358 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15203, d128358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15203, d128358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d16967 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d15204 q = 1) (hb : d128359 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15204, d128359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15204, d128359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15205 q = 1) (hb : d128367 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15205, d128367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15205, d128367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15206 q = 1) (hb : d128368 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15206, d128368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15206, d128368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128369 q = 1) (hb : d163564 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128369, d163564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128369, d163564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro34087 (p : Pattern) (ha : d128379 p = 1) (hb : d163583 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d17065 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d163578 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d128375 q = 1) (hb : d163579 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128375, d163579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128375, d163579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d17121 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d128376 q = 1) (hb : d163580 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128376, d163580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128376, d163580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d128377 q = 1) (hb : d163581 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128377, d163581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128377, d163581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128378 q = 1) (hb : d163582 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128378, d163582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128378, d163582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128379 q = 1) (hb : d163583 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128379, d163583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128379, d163583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34088 (p : Pattern) (ha : d128385 p = 1) (hb : d163589 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d16841 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15208 q = 1) (hb : d128363 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15208, d128363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34084 q ha hb
    | true =>
      simp only [d15208, d128363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34085 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d16990 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d15209 q = 1) (hb : d128364 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d15209, d128364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15209, d128364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d128365 q = 1) (hb : d163562 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128365, d163562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d128365, d163562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128366 q = 1) (hb : d163563 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128366, d163563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128366, d163563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128370 q = 1) (hb : d163565 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128370, d163565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128370, d163565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34086 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d16999 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d128371 q = 1) (hb : d163566 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128371, d163566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128371, d163566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d128372 q = 1) (hb : d163567 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128372, d163567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128372, d163567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d128373 q = 1) (hb : d163568 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128373, d163568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128373, d163568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d128374 q = 1) (hb : d163569 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128374, d163569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128374, d163569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128380 q = 1) (hb : d163584 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128380, d163584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128380, d163584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34087 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d17137 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d128381 q = 1) (hb : d163585 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128381, d163585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d128381, d163585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d128382 q = 1) (hb : d163586 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128382, d163586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d128382, d163586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d128383 q = 1) (hb : d163587 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128383, d163587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d128383, d163587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d128384 q = 1) (hb : d163588 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128384, d163588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d128384, d163588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d128385 q = 1) (hb : d163589 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128385, d163589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d128385, d163589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro34089 (p : Pattern) (ha : d128391 p = 1) (hb : d163595 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128386 q = 1) (hb : d163590 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128386, d163590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128386, d163590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34088 q ha hb
  have h2 (q : Pattern) (ha : d128387 q = 1) (hb : d163591 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128387, d163591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128387, d163591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128388 q = 1) (hb : d163592 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128388, d163592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128388, d163592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128389 q = 1) (hb : d163593 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128389, d163593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128389, d163593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128390 q = 1) (hb : d163594 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128390, d163594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128390, d163594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128391 q = 1) (hb : d163595 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128391, d163595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128391, d163595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34090 (p : Pattern) (ha : d15589 p = 1) (hb : d128400 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d17215 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d17224 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d17255 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d15584 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d15585 q = 1) (hb : d128396 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15585, d128396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15585, d128396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d17307 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d15586 q = 1) (hb : d128397 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15586, d128397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15586, d128397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15587 q = 1) (hb : d128398 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15587, d128398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15587, d128398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15588 q = 1) (hb : d128399 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15588, d128399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15588, d128399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15589 q = 1) (hb : d128400 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15589, d128400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15589, d128400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro34091 (p : Pattern) (ha : d15599 p = 1) (hb : d128405 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d17215 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d17224 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d17255 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d15584 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d15585 q = 1) (hb : d128396 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15585, d128396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15585, d128396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d17307 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d15586 q = 1) (hb : d128397 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15586, d128397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15586, d128397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15587 q = 1) (hb : d128398 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15587, d128398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15587, d128398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15588 q = 1) (hb : d128399 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15588, d128399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15588, d128399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d17317 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d17322 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d17325 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d15594 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d15595 q = 1) (hb : d128401 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15595, d128401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d15595, d128401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d17332 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d15596 q = 1) (hb : d128402 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15596, d128402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15596, d128402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d15597 q = 1) (hb : d128403 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15597, d128403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15597, d128403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d15598 q = 1) (hb : d128404 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15598, d128404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15598, d128404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d15599 q = 1) (hb : d128405 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15599, d128405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15599, d128405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro34092 (p : Pattern) (ha : d128412 p = 1) (hb : d163602 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d17325 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d15594 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d15595 q = 1) (hb : d128401 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15595, d128401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15595, d128401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d17332 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d15596 q = 1) (hb : d128402 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15596, d128402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15596, d128402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15597 q = 1) (hb : d128410 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15597, d128410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15597, d128410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15598 q = 1) (hb : d128411 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15598, d128411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15598, d128411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128412 q = 1) (hb : d163602 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128412, d163602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128412, d163602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro34093 (p : Pattern) (ha : d128422 p = 1) (hb : d163621 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d17429 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d163616 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d128418 q = 1) (hb : d163617 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128418, d163617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128418, d163617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d17485 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d128419 q = 1) (hb : d163618 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128419, d163618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128419, d163618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d128420 q = 1) (hb : d163619 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128420, d163619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128420, d163619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128421 q = 1) (hb : d163620 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128421, d163620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128421, d163620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128422 q = 1) (hb : d163621 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128422, d163621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128422, d163621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34094 (p : Pattern) (ha : d128428 p = 1) (hb : d163627 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d17207 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15600 q = 1) (hb : d128406 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15600, d128406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34090 q ha hb
    | true =>
      simp only [d15600, d128406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34091 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d17355 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d15601 q = 1) (hb : d128407 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d15601, d128407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15601, d128407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d128408 q = 1) (hb : d163600 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128408, d163600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d128408, d163600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128409 q = 1) (hb : d163601 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128409, d163601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128409, d163601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128413 q = 1) (hb : d163603 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128413, d163603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128413, d163603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34092 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d17364 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d128414 q = 1) (hb : d163604 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128414, d163604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128414, d163604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d128415 q = 1) (hb : d163605 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128415, d163605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128415, d163605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d128416 q = 1) (hb : d163606 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128416, d163606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128416, d163606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d128417 q = 1) (hb : d163607 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128417, d163607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128417, d163607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128423 q = 1) (hb : d163622 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128423, d163622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128423, d163622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34093 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d17501 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d128424 q = 1) (hb : d163623 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128424, d163623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d128424, d163623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d128425 q = 1) (hb : d163624 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128425, d163624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d128425, d163624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d128426 q = 1) (hb : d163625 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128426, d163625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d128426, d163625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d128427 q = 1) (hb : d163626 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128427, d163626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d128427, d163626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d128428 q = 1) (hb : d163627 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128428, d163627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d128428, d163627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro34095 (p : Pattern) (ha : d128434 p = 1) (hb : d163633 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128429 q = 1) (hb : d163628 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128429, d163628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128429, d163628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34094 q ha hb
  have h2 (q : Pattern) (ha : d128430 q = 1) (hb : d163629 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128430, d163629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128430, d163629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128431 q = 1) (hb : d163630 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128431, d163630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128431, d163630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128432 q = 1) (hb : d163631 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128432, d163631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128432, d163631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128433 q = 1) (hb : d163632 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128433, d163632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128433, d163632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128434 q = 1) (hb : d163633 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128434, d163633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128434, d163633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34096 (p : Pattern) (ha : d128440 p = 1) (hb : d163639 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d128269 q = 1) (hb : d163496 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d128269, d163496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34065 q ha hb
    | true =>
      simp only [d128269, d163496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34071 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d128309 q = 1) (hb : d163523 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d128309, d163523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128309, d163523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34077 q ha hb
  have h3 (q : Pattern) (ha : d128310 q = 1) (hb : d163524 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d128310, d163524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128310, d163524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128350 q = 1) (hb : d163559 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d128350, d163559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128350, d163559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34083 q ha hb
  have h5 (q : Pattern) (ha : d128351 q = 1) (hb : d163560 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d128351, d163560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128351, d163560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128352 q = 1) (hb : d163561 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d128352, d163561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128352, d163561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128392 q = 1) (hb : d163596 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d128392, d163596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128392, d163596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34089 q ha hb
  have h8 (q : Pattern) (ha : d128393 q = 1) (hb : d163597 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d128393, d163597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128393, d163597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128394 q = 1) (hb : d163598 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d128394, d163598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128394, d163598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d128395 q = 1) (hb : d163599 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d128395, d163599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128395, d163599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d128435 q = 1) (hb : d163634 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d128435, d163634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128435, d163634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34095 q ha hb
  have h12 (q : Pattern) (ha : d128436 q = 1) (hb : d163635 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d128436, d163635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128436, d163635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128437 q = 1) (hb : d163636 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d128437, d163636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128437, d163636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128438 q = 1) (hb : d163637 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d128438, d163637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128438, d163637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128439 q = 1) (hb : d163638 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d128439, d163638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128439, d163638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d128440 q = 1) (hb : d163639 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d128440, d163639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d128440, d163639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro34097 (p : Pattern) (ha : d128446 p = 1) (hb : d163645 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128441 q = 1) (hb : d163640 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d128441, d163640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34096 q ha hb
    | true =>
      simp only [d128441, d163640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d128442 q = 1) (hb : d163641 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d128442, d163641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128442, d163641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d128443 q = 1) (hb : d163642 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d128443, d163642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128443, d163642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d128444 q = 1) (hb : d163643 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d128444, d163643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128444, d163643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128445 q = 1) (hb : d163644 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d128445, d163644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128445, d163644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d128446 q = 1) (hb : d163645 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d128446, d163645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128446, d163645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34098 (p : Pattern) (ha : d128452 p = 1) (hb : d163651 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128447 q = 1) (hb : d163646 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d128447, d163646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34097 q ha hb
    | true =>
      simp only [d128447, d163646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d128448 q = 1) (hb : d163647 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d128448, d163647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128448, d163647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d128449 q = 1) (hb : d163648 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d128449, d163648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128449, d163648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d128450 q = 1) (hb : d163649 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d128450, d163649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128450, d163649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128451 q = 1) (hb : d163650 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d128451, d163650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128451, d163650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d128452 q = 1) (hb : d163651 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d128452, d163651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128452, d163651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34099 (p : Pattern) (ha : d128458 p = 1) (hb : d163657 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128453 q = 1) (hb : d163652 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d128453, d163652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34098 q ha hb
    | true =>
      simp only [d128453, d163652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d128454 q = 1) (hb : d163653 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d128454, d163653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128454, d163653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d128455 q = 1) (hb : d163654 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d128455, d163654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128455, d163654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d128456 q = 1) (hb : d163655 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d128456, d163655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128456, d163655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128457 q = 1) (hb : d163656 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d128457, d163656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128457, d163656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d128458 q = 1) (hb : d163657 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d128458, d163657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128458, d163657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34100 (p : Pattern) (ha : d128464 p = 1) (hb : d163663 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128459 q = 1) (hb : d163658 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d128459, d163658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34099 q ha hb
    | true =>
      simp only [d128459, d163658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d128460 q = 1) (hb : d163659 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d128460, d163659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128460, d163659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d128461 q = 1) (hb : d163660 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d128461, d163660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128461, d163660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d128462 q = 1) (hb : d163661 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d128462, d163661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128462, d163661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128463 q = 1) (hb : d163662 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d128463, d163662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128463, d163662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d128464 q = 1) (hb : d163663 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d128464, d163663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128464, d163663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34101 (p : Pattern) (ha : d128470 p = 1) (hb : d163669 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128465 q = 1) (hb : d163664 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d128465, d163664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34100 q ha hb
    | true =>
      simp only [d128465, d163664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d128466 q = 1) (hb : d163665 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d128466, d163665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128466, d163665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d128467 q = 1) (hb : d163666 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d128467, d163666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128467, d163666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d128468 q = 1) (hb : d163667 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d128468, d163667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128468, d163667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128469 q = 1) (hb : d163668 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d128469, d163668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128469, d163668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d128470 q = 1) (hb : d163669 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d128470, d163669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128470, d163669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34102 (p : Pattern) (ha : d128476 p = 1) (hb : d163675 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128471 q = 1) (hb : d163670 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d128471, d163670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34101 q ha hb
    | true =>
      simp only [d128471, d163670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d128472 q = 1) (hb : d163671 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d128472, d163671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128472, d163671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d128473 q = 1) (hb : d163672 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d128473, d163672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128473, d163672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d128474 q = 1) (hb : d163673 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d128474, d163673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128474, d163673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128475 q = 1) (hb : d163674 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d128475, d163674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128475, d163674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d128476 q = 1) (hb : d163675 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d128476, d163675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128476, d163675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34103 (p : Pattern) (ha : d128482 p = 1) (hb : d163681 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128477 q = 1) (hb : d163676 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d128477, d163676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34102 q ha hb
    | true =>
      simp only [d128477, d163676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d128478 q = 1) (hb : d163677 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d128478, d163677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128478, d163677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d128479 q = 1) (hb : d163678 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d128479, d163678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128479, d163678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d128480 q = 1) (hb : d163679 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d128480, d163679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128480, d163679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128481 q = 1) (hb : d163680 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d128481, d163680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128481, d163680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d128482 q = 1) (hb : d163681 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d128482, d163681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128482, d163681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34104 (p : Pattern) (ha : d125742 p = 1) (hb : d129471 p = 1) : d125742 p = 1 := by
  have h0 (q : Pattern) (ha : d125742 q = 1) (hb : d129471 q = 1) : d125742 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro34105 (p : Pattern) (ha : d129471 p = 1) (hb : d163681 p = 1) : d163681 p = 1 := by
  have h0 (q : Pattern) (ha : d129471 q = 1) (hb : d163681 q = 1) : d163681 q = 1 := by
    exact hb
  exact h0 p ha hb
theorem andIntro34106 (p : Pattern) (ha : d30 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d27 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d28 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d28, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d29 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d29, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d30 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d30, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34107 (p : Pattern) (ha : d36 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34106 q ha hb
    | true =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d34 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d35 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d35, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d35, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d36 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
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
theorem andIntro34108 (p : Pattern) (ha : d42 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34107 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d41 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d41, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d41, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d42 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
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
theorem andIntro34109 (p : Pattern) (ha : d48 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34108 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d45 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d47 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d48 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
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
theorem andIntro34110 (p : Pattern) (ha : d49 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34107 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d41 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d41, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d41, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d49 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
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
theorem andIntro34111 (p : Pattern) (ha : d55 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34108 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d45 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d47 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d50 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34110 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d51 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d52 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d55 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
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
theorem andIntro34112 (p : Pattern) (ha : d60 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d50 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34110 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d51 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d52 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d60 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
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
theorem andIntro34113 (p : Pattern) (ha : d71 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d69 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d70 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d70, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d70, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d71 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d71, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d71, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34114 (p : Pattern) (ha : d77 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d72 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34113 q ha hb
    | true =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d73 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d74 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d75 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d75, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d75, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d76 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d76, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d77 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
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
theorem andIntro34115 (p : Pattern) (ha : d83 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d78 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34114 q ha hb
    | true =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d79 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d80 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d80, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d80, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d81 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d81, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d81, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d82, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d83 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
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
theorem andIntro34116 (p : Pattern) (ha : d89 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34115 q ha hb
    | true =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d85 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d86 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d86, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d87 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d87, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d88 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
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
theorem andIntro34117 (p : Pattern) (ha : d95 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d56 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d56, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34109 q ha hb
    | true =>
      simp only [d56, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34111 q ha hb
  have h2 (q : Pattern) (ha : d57 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d57, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d57, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d58 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d59 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d59, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d59, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d61, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34112 q ha hb
  have h6 (q : Pattern) (ha : d62 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d62, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d63 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d63, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d63, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d64 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d64, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d64, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d65 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d65, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d65, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d90 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d90, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d90, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34116 q ha hb
  have h11 (q : Pattern) (ha : d91 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d91, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d91, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d92 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d92, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d93 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d93, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d93, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d94 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d95 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
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
theorem andIntro34118 (p : Pattern) (ha : d104 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34108 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d100 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d103 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d104 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
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
theorem andIntro34119 (p : Pattern) (ha : d111 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34108 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d100 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d103 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d50 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34110 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d107 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d109 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d110 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d111 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
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
theorem andIntro34120 (p : Pattern) (ha : d213 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34108 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d100 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d103 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d213 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
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
theorem andIntro34121 (p : Pattern) (ha : d116 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34107 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d116 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
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
theorem andIntro34122 (p : Pattern) (ha : d123 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34107 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d121 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
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
theorem andIntro34123 (p : Pattern) (ha : d13981 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d141 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d142 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d142, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d142, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13980 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13980, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13980, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d27 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d28 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d28, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d29 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d29, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d13981 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34124 (p : Pattern) (ha : d13987 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13982 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34123 q ha hb
    | true =>
      simp only [d13982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34106 q ha hb
  have h2 (q : Pattern) (ha : d13983 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13984 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34106 q ha hb
    | true =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13985 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d34 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13986 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13987 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro34125 (p : Pattern) (ha : d13993 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13988 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34124 q ha hb
    | true =>
      simp only [d13988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13989 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34107 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13990 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13991 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13992 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13993 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34126 (p : Pattern) (ha : d125417 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d117 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34121 q ha hb
    | true =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d118 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d124 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34122 q ha hb
    | true =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13994 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34125 q ha hb
    | true =>
      simp only [d13994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34108 q ha hb
  have h9 (q : Pattern) (ha : d125413 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d43 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34108 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d125414 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d125415 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d125415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d125416 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d125417 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro34127 (p : Pattern) (ha : d194 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34107 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d194 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
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
theorem andIntro34128 (p : Pattern) (ha : d199 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34107 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d121 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d199 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
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
theorem andIntro34129 (p : Pattern) (ha : d14000 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13988 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34124 q ha hb
    | true =>
      simp only [d13988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13989 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34107 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13990 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13991 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13992 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14000 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro34130 (p : Pattern) (ha : d125422 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d117 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34121 q ha hb
    | true =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d118 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d124 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34122 q ha hb
    | true =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13994 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34125 q ha hb
    | true =>
      simp only [d13994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34108 q ha hb
  have h9 (q : Pattern) (ha : d125413 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d43 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34108 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d125414 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d125415 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d125415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d125416 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d195 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34127 q ha hb
    | true =>
      simp only [d195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d196 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d197 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d198 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d200 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34128 q ha hb
    | true =>
      simp only [d200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d201 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d202 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d14001 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34129 q ha hb
    | true =>
      simp only [d14001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34110 q ha hb
  have h23 (q : Pattern) (ha : d125418 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d125418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d50 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34110 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d51 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d125419 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d125419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d125420 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d125420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d125421 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d125421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d125422 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d125422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro34131 (p : Pattern) (ha : d125429 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14001 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34129 q ha hb
    | true =>
      simp only [d14001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34110 q ha hb
  have h2 (q : Pattern) (ha : d125418 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d50 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34110 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125419 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125427 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125428 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125429 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34132 (p : Pattern) (ha : d14020 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d228 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d229 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d229, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d14019 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14019, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14019, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d68 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d69 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d69, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d70 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d70, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d70, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d14020 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34133 (p : Pattern) (ha : d14026 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14021 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34132 q ha hb
    | true =>
      simp only [d14021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34113 q ha hb
  have h2 (q : Pattern) (ha : d14022 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14023 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d72 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34113 q ha hb
    | true =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d73 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14024 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d75 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d75, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d75, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d14025 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14026 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d14026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro34134 (p : Pattern) (ha : d14032 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14027 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34133 q ha hb
    | true =>
      simp only [d14027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14028 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d78 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34114 q ha hb
    | true =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d79 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14029 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14030 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14031 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14032 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro34135 (p : Pattern) (ha : d125439 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14033 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34134 q ha hb
    | true =>
      simp only [d14033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34115 q ha hb
  have h2 (q : Pattern) (ha : d125435 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d84 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34115 q ha hb
    | true =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125436 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125437 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125438 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125439 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34136 (p : Pattern) (ha : d125445 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34118 q ha hb
  have h2 (q : Pattern) (ha : d106 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d112 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34118 q ha hb
    | true =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34119 q ha hb
  have h4 (q : Pattern) (ha : d113 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d114 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125423 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34126 q ha hb
    | true =>
      simp only [d125423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34130 q ha hb
  have h7 (q : Pattern) (ha : d214 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34120 q ha hb
    | true =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d125424 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d125424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d125425 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d125426 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d125430 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34131 q ha hb
  have h12 (q : Pattern) (ha : d125431 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d125431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d125432 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d125432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d125433 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d125433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d125434 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d125434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d125440 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34135 q ha hb
  have h17 (q : Pattern) (ha : d125441 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d125441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d125442 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d125442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d125443 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d125443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d125444 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d125444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d125445 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d125445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d125445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro34137 (p : Pattern) (ha : d406 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d50 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34110 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d107 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d110 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d406 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
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
theorem andIntro34138 (p : Pattern) (ha : d462 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34115 q ha hb
    | true =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d458 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d459 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d460 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d461 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d462 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
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
theorem andIntro34139 (p : Pattern) (ha : d14054 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13994 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34125 q ha hb
    | true =>
      simp only [d13994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34108 q ha hb
  have h2 (q : Pattern) (ha : d14050 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14051 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14052 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14053 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14054 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34140 (p : Pattern) (ha : d14061 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13994 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34125 q ha hb
    | true =>
      simp only [d13994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34108 q ha hb
  have h2 (q : Pattern) (ha : d14050 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14051 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14052 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14053 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14001 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34129 q ha hb
    | true =>
      simp only [d14001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34110 q ha hb
  have h7 (q : Pattern) (ha : d14057 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14058 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d14059 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14060 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14061 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro34141 (p : Pattern) (ha : d14141 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13994 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34125 q ha hb
    | true =>
      simp only [d13994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34108 q ha hb
  have h2 (q : Pattern) (ha : d14050 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14051 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14052 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14053 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34108 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d100 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d102 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d103 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14141 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro34142 (p : Pattern) (ha : d14066 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13988 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34124 q ha hb
    | true =>
      simp only [d13988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13989 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34107 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13990 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13991 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14065 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14066 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34143 (p : Pattern) (ha : d14073 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13988 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34124 q ha hb
    | true =>
      simp only [d13988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13989 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34107 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13990 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14071 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14072 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14073 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34144 (p : Pattern) (ha : d14079 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d321 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d322 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d322, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d14077 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14077, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14077, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d12493 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d12494 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12494, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d12494, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d14078 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14078, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14078, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d14079 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34145 (p : Pattern) (ha : d14085 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14080 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34144 q ha hb
    | true =>
      simp only [d14080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34123 q ha hb
  have h2 (q : Pattern) (ha : d14081 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14082 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13982 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34123 q ha hb
    | true =>
      simp only [d13982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34106 q ha hb
  have h5 (q : Pattern) (ha : d13983 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13984 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14083 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34106 q ha hb
    | true =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d32 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13985 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d14084 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d14085 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d14085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro34146 (p : Pattern) (ha : d14091 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14086 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34145 q ha hb
    | true =>
      simp only [d14086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14087 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13988 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34124 q ha hb
    | true =>
      simp only [d13988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13989 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14088 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14089 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14090 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14091 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34147 (p : Pattern) (ha : d14112 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13988 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34124 q ha hb
    | true =>
      simp only [d13988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13989 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14109 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14110 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14111 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14112 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34148 (p : Pattern) (ha : d125455 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14067 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34142 q ha hb
    | true =>
      simp only [d14067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34121 q ha hb
  have h2 (q : Pattern) (ha : d14068 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14069 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14070 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14074 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34143 q ha hb
    | true =>
      simp only [d14074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34122 q ha hb
  have h6 (q : Pattern) (ha : d14075 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14076 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14092 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34146 q ha hb
    | true =>
      simp only [d14092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34125 q ha hb
  have h9 (q : Pattern) (ha : d125451 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d14113 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34147 q ha hb
    | true =>
      simp only [d14113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d14114 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d14114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d125452 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d125453 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d125453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d125454 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d125455 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro34149 (p : Pattern) (ha : d14119 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13988 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34124 q ha hb
    | true =>
      simp only [d13988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13989 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34107 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13990 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13991 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14065 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14119 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro34150 (p : Pattern) (ha : d14124 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13988 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34124 q ha hb
    | true =>
      simp only [d13988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13989 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34107 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13990 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14071 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14072 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14124 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro34151 (p : Pattern) (ha : d14128 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14086 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34145 q ha hb
    | true =>
      simp only [d14086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14087 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13988 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34124 q ha hb
    | true =>
      simp only [d13988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13989 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14088 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14089 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14090 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14128 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro34152 (p : Pattern) (ha : d14133 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13988 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34124 q ha hb
    | true =>
      simp only [d13988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13989 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14109 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14110 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14111 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14133 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34153 (p : Pattern) (ha : d125460 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14067 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34142 q ha hb
    | true =>
      simp only [d14067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34121 q ha hb
  have h2 (q : Pattern) (ha : d14068 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14069 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14070 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14074 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34143 q ha hb
    | true =>
      simp only [d14074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34122 q ha hb
  have h6 (q : Pattern) (ha : d14075 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14076 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14092 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34146 q ha hb
    | true =>
      simp only [d14092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34125 q ha hb
  have h9 (q : Pattern) (ha : d125451 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d14113 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34147 q ha hb
    | true =>
      simp only [d14113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d14114 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d14114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d125452 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d125453 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d125453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d125454 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d14120 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34149 q ha hb
    | true =>
      simp only [d14120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34127 q ha hb
  have h16 (q : Pattern) (ha : d14121 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d14122 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d14122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d14123 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d14125 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34150 q ha hb
    | true =>
      simp only [d14125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34128 q ha hb
  have h20 (q : Pattern) (ha : d14126 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d14127 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d14127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d14129 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34151 q ha hb
    | true =>
      simp only [d14129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34129 q ha hb
  have h23 (q : Pattern) (ha : d125456 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d125456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d14134 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34152 q ha hb
    | true =>
      simp only [d14134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d14135 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d14135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d125457 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d125457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d125458 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d125458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d125459 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d125459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d125460 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d125460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro34154 (p : Pattern) (ha : d125467 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14129 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34151 q ha hb
    | true =>
      simp only [d14129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34129 q ha hb
  have h2 (q : Pattern) (ha : d125456 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d14134 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34152 q ha hb
    | true =>
      simp only [d14134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14135 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125457 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125465 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125466 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125467 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34155 (p : Pattern) (ha : d14156 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d414 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d415 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d415, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d415, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d14154 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14154, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14154, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d12601 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d12602 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12602, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d12602, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d14155 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14155, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14155, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d14156 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34156 (p : Pattern) (ha : d14162 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14157 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34155 q ha hb
    | true =>
      simp only [d14157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34132 q ha hb
  have h2 (q : Pattern) (ha : d14158 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14159 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14021 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34132 q ha hb
    | true =>
      simp only [d14021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34113 q ha hb
  have h5 (q : Pattern) (ha : d14022 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14023 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14160 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d72 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34113 q ha hb
    | true =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d73 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d74 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14024 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d14161 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d14162 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d14162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro34157 (p : Pattern) (ha : d14168 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14163 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34156 q ha hb
    | true =>
      simp only [d14163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14164 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14027 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34133 q ha hb
    | true =>
      simp only [d14027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14028 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14165 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14166 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14167 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14168 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro34158 (p : Pattern) (ha : d14189 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14027 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34133 q ha hb
    | true =>
      simp only [d14027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14028 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14186 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14187 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14188 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14189 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34159 (p : Pattern) (ha : d125477 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14169 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34157 q ha hb
    | true =>
      simp only [d14169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34134 q ha hb
  have h2 (q : Pattern) (ha : d125473 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d14190 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34158 q ha hb
    | true =>
      simp only [d14190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14191 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125474 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125475 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125476 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125477 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34160 (p : Pattern) (ha : d125483 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14055 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34139 q ha hb
  have h2 (q : Pattern) (ha : d14056 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d14062 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34139 q ha hb
    | true =>
      simp only [d14062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34140 q ha hb
  have h4 (q : Pattern) (ha : d14063 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14064 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d14064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125461 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34148 q ha hb
    | true =>
      simp only [d125461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34153 q ha hb
  have h7 (q : Pattern) (ha : d14142 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34141 q ha hb
    | true =>
      simp only [d14142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34119 q ha hb
  have h8 (q : Pattern) (ha : d125462 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d125462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d125463 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d125464 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d125468 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34154 q ha hb
  have h12 (q : Pattern) (ha : d407 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34137 q ha hb
  have h13 (q : Pattern) (ha : d125469 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d125469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d125470 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d125470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d125471 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d125471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d125472 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d125472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d125478 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34159 q ha hb
  have h18 (q : Pattern) (ha : d463 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34138 q ha hb
  have h19 (q : Pattern) (ha : d125479 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d125479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d125480 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d125480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d125481 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d125481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d125482 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d125482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d125483 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d125483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d125483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro34161 (p : Pattern) (ha : d125489 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d96, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d96, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34117 q ha hb
  have h2 (q : Pattern) (ha : d97 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d97, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d97, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d98 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d98, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d98, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d99 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d125446 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d125446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34136 q ha hb
  have h6 (q : Pattern) (ha : d125447 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d125447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125448 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d125448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125449 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d125449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d125450 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d125450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d125484 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d125484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34160 q ha hb
  have h11 (q : Pattern) (ha : d125485 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d125485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d125486 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d125486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d125487 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d125487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d125488 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d125488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d125489 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d125489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro34162 (p : Pattern) (ha : d14210 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14080 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34144 q ha hb
    | true =>
      simp only [d14080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34123 q ha hb
  have h2 (q : Pattern) (ha : d14081 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14082 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13982 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34123 q ha hb
    | true =>
      simp only [d13982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34106 q ha hb
  have h5 (q : Pattern) (ha : d13983 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13984 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14083 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14208 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d14209 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14210 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d14210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro34163 (p : Pattern) (ha : d14214 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13982 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34123 q ha hb
    | true =>
      simp only [d13982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34106 q ha hb
  have h2 (q : Pattern) (ha : d13983 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13984 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14208 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14213 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14214 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34164 (p : Pattern) (ha : d14220 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14211 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34162 q ha hb
    | true =>
      simp only [d14211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14212 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14215 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34163 q ha hb
    | true =>
      simp only [d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14216 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14217 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14218 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14219 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14220 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34165 (p : Pattern) (ha : d14224 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14215 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34163 q ha hb
    | true =>
      simp only [d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14216 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14221 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14222 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14223 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14224 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34166 (p : Pattern) (ha : d14230 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14225 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34164 q ha hb
    | true =>
      simp only [d14225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34165 q ha hb
  have h2 (q : Pattern) (ha : d14226 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14227 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14228 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14229 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14230 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34167 (p : Pattern) (ha : d14233 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14211 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34162 q ha hb
    | true =>
      simp only [d14211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14212 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14215 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34163 q ha hb
    | true =>
      simp only [d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14216 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14217 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14218 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14219 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14233 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro34168 (p : Pattern) (ha : d14234 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14215 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34163 q ha hb
    | true =>
      simp only [d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14216 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14221 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14222 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14223 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14234 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34169 (p : Pattern) (ha : d14240 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14225 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34164 q ha hb
    | true =>
      simp only [d14225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34165 q ha hb
  have h2 (q : Pattern) (ha : d14226 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14227 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14228 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14229 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14235 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34167 q ha hb
    | true =>
      simp only [d14235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34168 q ha hb
  have h7 (q : Pattern) (ha : d14236 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14237 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d14238 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14239 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14240 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro34170 (p : Pattern) (ha : d14349 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14225 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34164 q ha hb
    | true =>
      simp only [d14225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34165 q ha hb
  have h2 (q : Pattern) (ha : d14226 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14227 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14228 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14229 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14344 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34165 q ha hb
    | true =>
      simp only [d14344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14345 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14346 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d14347 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14348 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14349 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro34171 (p : Pattern) (ha : d14355 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14344 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34165 q ha hb
    | true =>
      simp only [d14344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14345 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14346 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14347 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14348 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14350 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34168 q ha hb
    | true =>
      simp only [d14350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14351 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14352 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d14353 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14354 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14355 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro34172 (p : Pattern) (ha : d14364 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14350 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34168 q ha hb
    | true =>
      simp only [d14350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14351 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14352 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14353 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14354 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14364 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34173 (p : Pattern) (ha : d14395 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14021 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34132 q ha hb
    | true =>
      simp only [d14021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34113 q ha hb
  have h2 (q : Pattern) (ha : d14022 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14023 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14385 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14394 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14395 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34174 (p : Pattern) (ha : d14447 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14396 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34173 q ha hb
    | true =>
      simp only [d14396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14397 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14444 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14445 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14446 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14447 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34175 (p : Pattern) (ha : d14453 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14448 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34174 q ha hb
    | true =>
      simp only [d14448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14449 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14450 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14451 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14452 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14453 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34176 (p : Pattern) (ha : d14245 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14211 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34162 q ha hb
    | true =>
      simp only [d14211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14212 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14215 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34163 q ha hb
    | true =>
      simp only [d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14216 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14217 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14218 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14244 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14245 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34177 (p : Pattern) (ha : d14247 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14215 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34163 q ha hb
    | true =>
      simp only [d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14216 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14221 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14222 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14246 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14247 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34178 (p : Pattern) (ha : d14254 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14211 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34162 q ha hb
    | true =>
      simp only [d14211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14212 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14215 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34163 q ha hb
    | true =>
      simp only [d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14216 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14217 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14252 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14253 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14254 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34179 (p : Pattern) (ha : d14257 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14215 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34163 q ha hb
    | true =>
      simp only [d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14216 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14221 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14255 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14256 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14257 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34180 (p : Pattern) (ha : d14263 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d545 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d546 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d546, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d546, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d14261 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14261, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14261, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d12748 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d12749 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12749, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d12749, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d14262 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14262, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14262, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d14263 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34181 (p : Pattern) (ha : d14267 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d12493 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12494 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12494, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d12494, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d14078 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14078, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14078, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d27 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d28 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d28, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d29 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d29, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d14267 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34182 (p : Pattern) (ha : d14273 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14264 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34180 q ha hb
    | true =>
      simp only [d14264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34144 q ha hb
  have h2 (q : Pattern) (ha : d14265 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14266 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14268 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34144 q ha hb
    | true =>
      simp only [d14268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34181 q ha hb
  have h5 (q : Pattern) (ha : d14269 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14270 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14271 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14080 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34144 q ha hb
    | true =>
      simp only [d14080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34123 q ha hb
  have h9 (q : Pattern) (ha : d14081 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14082 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13982 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34123 q ha hb
    | true =>
      simp only [d13982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34106 q ha hb
  have h12 (q : Pattern) (ha : d13983 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d13984 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d14083 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d14083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d14272 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d14273 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d14273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro34183 (p : Pattern) (ha : d14279 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14274 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34182 q ha hb
    | true =>
      simp only [d14274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14275 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14211 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34162 q ha hb
    | true =>
      simp only [d14211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14212 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14276 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14277 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14278 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14279 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34184 (p : Pattern) (ha : d14312 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14211 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34162 q ha hb
    | true =>
      simp only [d14211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14212 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14309 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14310 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14311 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14312 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34185 (p : Pattern) (ha : d125494 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14248 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34176 q ha hb
    | true =>
      simp only [d14248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34177 q ha hb
  have h2 (q : Pattern) (ha : d14249 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14250 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14251 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14258 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34178 q ha hb
    | true =>
      simp only [d14258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34179 q ha hb
  have h6 (q : Pattern) (ha : d14259 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14260 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14280 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34183 q ha hb
    | true =>
      simp only [d14280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34164 q ha hb
  have h9 (q : Pattern) (ha : d125490 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d14313 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34184 q ha hb
    | true =>
      simp only [d14313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d14314 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d14314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d125491 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d125492 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d125492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d125493 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d125494 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro34186 (p : Pattern) (ha : d14319 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14211 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34162 q ha hb
    | true =>
      simp only [d14211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14212 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14215 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34163 q ha hb
    | true =>
      simp only [d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14216 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14217 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14218 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14244 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14319 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro34187 (p : Pattern) (ha : d14320 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14215 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34163 q ha hb
    | true =>
      simp only [d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14216 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14221 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14222 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14246 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14320 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34188 (p : Pattern) (ha : d14325 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14211 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34162 q ha hb
    | true =>
      simp only [d14211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14212 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14215 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34163 q ha hb
    | true =>
      simp only [d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14216 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14217 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14252 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14253 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14325 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro34189 (p : Pattern) (ha : d14326 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14215 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34163 q ha hb
    | true =>
      simp only [d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14216 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14221 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14255 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14256 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14326 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34190 (p : Pattern) (ha : d14330 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14274 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34182 q ha hb
    | true =>
      simp only [d14274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14275 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14211 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34162 q ha hb
    | true =>
      simp only [d14211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14212 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14276 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14277 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14278 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14330 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro34191 (p : Pattern) (ha : d14336 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14211 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34162 q ha hb
    | true =>
      simp only [d14211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14212 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14309 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14310 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14311 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14336 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34192 (p : Pattern) (ha : d125499 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14248 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34176 q ha hb
    | true =>
      simp only [d14248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34177 q ha hb
  have h2 (q : Pattern) (ha : d14249 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14250 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14251 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14258 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34178 q ha hb
    | true =>
      simp only [d14258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34179 q ha hb
  have h6 (q : Pattern) (ha : d14259 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14260 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14280 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34183 q ha hb
    | true =>
      simp only [d14280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34164 q ha hb
  have h9 (q : Pattern) (ha : d125490 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d14313 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34184 q ha hb
    | true =>
      simp only [d14313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d14314 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d14314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d125491 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d125492 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d125492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d125493 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d14321 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34186 q ha hb
    | true =>
      simp only [d14321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34187 q ha hb
  have h16 (q : Pattern) (ha : d14322 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d14323 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d14323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d14324 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d14327 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34188 q ha hb
    | true =>
      simp only [d14327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34189 q ha hb
  have h20 (q : Pattern) (ha : d14328 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d14329 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d14329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d14331 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34190 q ha hb
    | true =>
      simp only [d14331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34167 q ha hb
  have h23 (q : Pattern) (ha : d125495 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d125495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d14337 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34191 q ha hb
    | true =>
      simp only [d14337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d14338 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d14338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d125496 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d125496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d125497 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d125497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d125498 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d125498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d125499 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d125499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro34193 (p : Pattern) (ha : d125506 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14331 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34190 q ha hb
    | true =>
      simp only [d14331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34167 q ha hb
  have h2 (q : Pattern) (ha : d125495 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d14337 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34191 q ha hb
    | true =>
      simp only [d14337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14338 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125496 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125504 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125505 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125506 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34194 (p : Pattern) (ha : d14372 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d661 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d662 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d662, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d662, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d14370 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14370, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14370, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d12860 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d12861 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12861, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d12861, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d14371 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14371, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14371, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d14372 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34195 (p : Pattern) (ha : d14376 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d12601 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12602 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12602, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d12602, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d14155 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14155, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14155, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d68 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d69 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d69, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d70 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d70, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d70, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d14376 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34196 (p : Pattern) (ha : d14382 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14373 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34194 q ha hb
    | true =>
      simp only [d14373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34155 q ha hb
  have h2 (q : Pattern) (ha : d14374 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14375 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14377 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34155 q ha hb
    | true =>
      simp only [d14377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34195 q ha hb
  have h5 (q : Pattern) (ha : d14378 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14379 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14380 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14157 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34155 q ha hb
    | true =>
      simp only [d14157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34132 q ha hb
  have h9 (q : Pattern) (ha : d14158 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14159 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14021 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34132 q ha hb
    | true =>
      simp only [d14021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34113 q ha hb
  have h12 (q : Pattern) (ha : d14022 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d14023 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d14160 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d14160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d14381 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d14382 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d14382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro34197 (p : Pattern) (ha : d14387 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14157 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34155 q ha hb
    | true =>
      simp only [d14157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34132 q ha hb
  have h2 (q : Pattern) (ha : d14158 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14159 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14021 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34132 q ha hb
    | true =>
      simp only [d14021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34113 q ha hb
  have h5 (q : Pattern) (ha : d14022 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14023 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14160 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14385 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d14386 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14387 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d14387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro34198 (p : Pattern) (ha : d14393 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14383 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34196 q ha hb
    | true =>
      simp only [d14383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14384 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14388 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34197 q ha hb
    | true =>
      simp only [d14388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14389 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14390 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14391 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14392 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14393 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro34199 (p : Pattern) (ha : d14401 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14388 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34197 q ha hb
    | true =>
      simp only [d14388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14389 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14396 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34173 q ha hb
    | true =>
      simp only [d14396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14397 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14398 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14399 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14400 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14401 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro34200 (p : Pattern) (ha : d14436 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14388 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34197 q ha hb
    | true =>
      simp only [d14388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14389 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14433 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14434 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14435 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14436 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34201 (p : Pattern) (ha : d125516 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14402 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34198 q ha hb
    | true =>
      simp only [d14402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34199 q ha hb
  have h2 (q : Pattern) (ha : d125512 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d14437 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34200 q ha hb
    | true =>
      simp only [d14437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14438 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125513 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125514 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125515 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125516 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34202 (p : Pattern) (ha : d125522 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14231 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34166 q ha hb
  have h2 (q : Pattern) (ha : d14232 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d14241 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34166 q ha hb
    | true =>
      simp only [d14241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34169 q ha hb
  have h4 (q : Pattern) (ha : d14242 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14243 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d14243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125500 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34185 q ha hb
    | true =>
      simp only [d125500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34192 q ha hb
  have h7 (q : Pattern) (ha : d14356 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34170 q ha hb
    | true =>
      simp only [d14356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34171 q ha hb
  have h8 (q : Pattern) (ha : d125501 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d125501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d125502 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d125503 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d125507 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34193 q ha hb
  have h12 (q : Pattern) (ha : d14365 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34172 q ha hb
  have h13 (q : Pattern) (ha : d125508 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d125508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d125509 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d125509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d125510 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d125510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d125511 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d125511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d125517 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34201 q ha hb
  have h18 (q : Pattern) (ha : d14454 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34175 q ha hb
  have h19 (q : Pattern) (ha : d125518 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d125518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d125519 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d125519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d125520 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d125520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d125521 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d125521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d125522 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d125522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d125522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro34203 (p : Pattern) (ha : d125528 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125523 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d125523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34202 q ha hb
  have h2 (q : Pattern) (ha : d125524 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d125524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d125525 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d125525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d125526 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d125526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d125527 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d125527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125528 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d125528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34204 (p : Pattern) (ha : d762 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d754 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d754, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d757 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d757, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d757, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d762 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34205 (p : Pattern) (ha : d14467 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d321 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d322 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d322, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d14077 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14077, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14077, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d753 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d754 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d754, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d757 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d757, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d757, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d14467 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34206 (p : Pattern) (ha : d14477 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14468 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34180 q ha hb
    | true =>
      simp only [d14468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34205 q ha hb
  have h2 (q : Pattern) (ha : d14469 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14470 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14471 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34205 q ha hb
    | true =>
      simp only [d14471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34204 q ha hb
  have h5 (q : Pattern) (ha : d14472 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14473 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14474 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14475 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d14476 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14477 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d14477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro34207 (p : Pattern) (ha : d14481 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14471 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34205 q ha hb
    | true =>
      simp only [d14471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34204 q ha hb
  have h2 (q : Pattern) (ha : d14472 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14473 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14475 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14480 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14481 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34208 (p : Pattern) (ha : d14487 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14478 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34206 q ha hb
    | true =>
      simp only [d14478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14479 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14482 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34207 q ha hb
    | true =>
      simp only [d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14483 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14484 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14485 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14486 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14487 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34209 (p : Pattern) (ha : d14491 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14482 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34207 q ha hb
    | true =>
      simp only [d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14483 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14488 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14489 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14490 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14491 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34210 (p : Pattern) (ha : d14497 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14492 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34208 q ha hb
    | true =>
      simp only [d14492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34209 q ha hb
  have h2 (q : Pattern) (ha : d14493 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14494 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14495 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14496 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14497 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34211 (p : Pattern) (ha : d14500 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14478 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34206 q ha hb
    | true =>
      simp only [d14478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14479 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14482 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34207 q ha hb
    | true =>
      simp only [d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14483 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14484 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14485 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14486 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14500 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro34212 (p : Pattern) (ha : d14501 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14482 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34207 q ha hb
    | true =>
      simp only [d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14483 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14488 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14489 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14490 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14501 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34213 (p : Pattern) (ha : d14507 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14492 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34208 q ha hb
    | true =>
      simp only [d14492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34209 q ha hb
  have h2 (q : Pattern) (ha : d14493 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14494 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14495 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14496 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14502 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34211 q ha hb
    | true =>
      simp only [d14502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34212 q ha hb
  have h7 (q : Pattern) (ha : d14503 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14504 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d14505 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14506 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14507 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro34214 (p : Pattern) (ha : d14622 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14492 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34208 q ha hb
    | true =>
      simp only [d14492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34209 q ha hb
  have h2 (q : Pattern) (ha : d14493 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14494 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14495 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14496 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14617 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34209 q ha hb
    | true =>
      simp only [d14617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14618 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14619 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d14620 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14621 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14622 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro34215 (p : Pattern) (ha : d14628 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14617 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34209 q ha hb
    | true =>
      simp only [d14617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14618 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14619 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14620 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14621 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14623 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34212 q ha hb
    | true =>
      simp only [d14623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14624 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14625 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d14626 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14627 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14628 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro34216 (p : Pattern) (ha : d14637 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14623 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34212 q ha hb
    | true =>
      simp only [d14623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14624 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14625 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14626 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14627 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14637 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34217 (p : Pattern) (ha : d986 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d973 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d974 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d974, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d980 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d980, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d980, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d986 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34218 (p : Pattern) (ha : d14658 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d414 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d415 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d415, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d415, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d14154 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14154, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14154, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d973 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d974 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d974, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d980 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d980, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d980, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d14658 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34219 (p : Pattern) (ha : d14680 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14662 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34218 q ha hb
    | true =>
      simp only [d14662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34217 q ha hb
  have h2 (q : Pattern) (ha : d14663 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14664 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14670 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14679 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14680 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34220 (p : Pattern) (ha : d14736 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14681 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34219 q ha hb
    | true =>
      simp only [d14681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14682 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14733 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14734 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14735 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14736 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34221 (p : Pattern) (ha : d14742 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14737 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34220 q ha hb
    | true =>
      simp only [d14737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14738 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14739 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14740 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14741 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14742 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34222 (p : Pattern) (ha : d14512 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14478 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34206 q ha hb
    | true =>
      simp only [d14478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14479 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14482 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34207 q ha hb
    | true =>
      simp only [d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14483 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14484 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14485 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14511 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14512 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34223 (p : Pattern) (ha : d14514 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14482 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34207 q ha hb
    | true =>
      simp only [d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14483 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14488 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14489 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14513 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14514 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34224 (p : Pattern) (ha : d14521 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14478 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34206 q ha hb
    | true =>
      simp only [d14478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14479 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14482 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34207 q ha hb
    | true =>
      simp only [d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14483 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14484 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14519 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14520 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14521 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34225 (p : Pattern) (ha : d14524 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14482 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34207 q ha hb
    | true =>
      simp only [d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14483 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14488 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14522 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14523 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14524 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34226 (p : Pattern) (ha : d14532 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d837 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d837, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d837, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d14528 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14528, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14528, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d14529 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d14530 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14530, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d14530, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d14531 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14531, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14531, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d14532 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34227 (p : Pattern) (ha : d14536 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d12748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12749 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12749, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d12749, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d14262 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14262, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14262, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d753 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d754 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d754, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d757 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d757, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d757, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d14536 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34228 (p : Pattern) (ha : d14542 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14533 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34226 q ha hb
    | true =>
      simp only [d14533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34180 q ha hb
  have h2 (q : Pattern) (ha : d14534 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14535 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14537 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34180 q ha hb
    | true =>
      simp only [d14537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34227 q ha hb
  have h5 (q : Pattern) (ha : d14538 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14539 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14540 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14468 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34180 q ha hb
    | true =>
      simp only [d14468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34205 q ha hb
  have h9 (q : Pattern) (ha : d14469 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14470 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14471 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34205 q ha hb
    | true =>
      simp only [d14471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34204 q ha hb
  have h12 (q : Pattern) (ha : d14472 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d14473 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d14474 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d14474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d14541 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d14542 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d14542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro34229 (p : Pattern) (ha : d14548 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14543 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34228 q ha hb
    | true =>
      simp only [d14543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14544 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14478 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34206 q ha hb
    | true =>
      simp only [d14478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14479 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14545 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14546 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14547 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14548 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34230 (p : Pattern) (ha : d14585 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14478 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34206 q ha hb
    | true =>
      simp only [d14478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14479 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14582 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14583 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14584 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14585 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro34231 (p : Pattern) (ha : d125534 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14515 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34222 q ha hb
    | true =>
      simp only [d14515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34223 q ha hb
  have h2 (q : Pattern) (ha : d14516 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14517 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14518 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14525 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34224 q ha hb
    | true =>
      simp only [d14525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34225 q ha hb
  have h6 (q : Pattern) (ha : d14526 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14527 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14549 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34229 q ha hb
    | true =>
      simp only [d14549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34208 q ha hb
  have h9 (q : Pattern) (ha : d125530 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d14586 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34230 q ha hb
    | true =>
      simp only [d14586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d14587 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d14587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d125531 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d125532 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d125532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d125533 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d125534 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro34232 (p : Pattern) (ha : d14592 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14478 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34206 q ha hb
    | true =>
      simp only [d14478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14479 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14482 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34207 q ha hb
    | true =>
      simp only [d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14483 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14484 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14485 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14511 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14592 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro34233 (p : Pattern) (ha : d14593 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14482 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34207 q ha hb
    | true =>
      simp only [d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14483 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14488 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14489 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14513 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14593 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34234 (p : Pattern) (ha : d14598 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14478 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34206 q ha hb
    | true =>
      simp only [d14478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14479 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14482 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34207 q ha hb
    | true =>
      simp only [d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14483 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14484 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14519 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14520 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14598 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro34235 (p : Pattern) (ha : d14599 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14482 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34207 q ha hb
    | true =>
      simp only [d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14483 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14488 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14522 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14523 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14599 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34236 (p : Pattern) (ha : d14603 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14543 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34228 q ha hb
    | true =>
      simp only [d14543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14544 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14478 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34206 q ha hb
    | true =>
      simp only [d14478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14479 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14545 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14546 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14547 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14603 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro34237 (p : Pattern) (ha : d14609 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14478 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34206 q ha hb
    | true =>
      simp only [d14478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14479 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14582 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14583 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14584 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14609 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34238 (p : Pattern) (ha : d125539 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14515 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34222 q ha hb
    | true =>
      simp only [d14515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34223 q ha hb
  have h2 (q : Pattern) (ha : d14516 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14517 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14518 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14525 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34224 q ha hb
    | true =>
      simp only [d14525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34225 q ha hb
  have h6 (q : Pattern) (ha : d14526 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14527 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14549 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34229 q ha hb
    | true =>
      simp only [d14549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34208 q ha hb
  have h9 (q : Pattern) (ha : d125530 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d14586 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34230 q ha hb
    | true =>
      simp only [d14586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d14587 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d14587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d125531 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d125532 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d125532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d125533 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d14594 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34232 q ha hb
    | true =>
      simp only [d14594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34233 q ha hb
  have h16 (q : Pattern) (ha : d14595 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d14596 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d14596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d14597 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d14600 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34234 q ha hb
    | true =>
      simp only [d14600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34235 q ha hb
  have h20 (q : Pattern) (ha : d14601 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d14602 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d14602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d14604 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34236 q ha hb
    | true =>
      simp only [d14604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34211 q ha hb
  have h23 (q : Pattern) (ha : d125535 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d125535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d14610 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34237 q ha hb
    | true =>
      simp only [d14610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d14611 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d14611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d125536 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d125536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d125537 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d125537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d125538 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d125538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d125539 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d125539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro34239 (p : Pattern) (ha : d125546 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14604 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34236 q ha hb
    | true =>
      simp only [d14604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34211 q ha hb
  have h2 (q : Pattern) (ha : d125535 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d14610 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34237 q ha hb
    | true =>
      simp only [d14610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14611 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125536 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125544 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125545 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125546 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34240 (p : Pattern) (ha : d14649 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d967 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d968 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d968, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d968, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d14643 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14643, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14643, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d14646 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d14647 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14647, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d14647, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d14648 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14648, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14648, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d14649 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34241 (p : Pattern) (ha : d14653 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d12860 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12861 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12861, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d12861, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d14371 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14371, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14371, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d973 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d974 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d974, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d980 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d980, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d980, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d14653 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34242 (p : Pattern) (ha : d14667 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14650 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34240 q ha hb
    | true =>
      simp only [d14650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34194 q ha hb
  have h2 (q : Pattern) (ha : d14651 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14652 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14654 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34194 q ha hb
    | true =>
      simp only [d14654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34241 q ha hb
  have h5 (q : Pattern) (ha : d14655 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14656 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14657 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14659 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34194 q ha hb
    | true =>
      simp only [d14659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34218 q ha hb
  have h9 (q : Pattern) (ha : d14660 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14661 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14662 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34218 q ha hb
    | true =>
      simp only [d14662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34217 q ha hb
  have h12 (q : Pattern) (ha : d14663 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d14664 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d14665 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d14665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d14666 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d14667 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d14667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro34243 (p : Pattern) (ha : d14672 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14659 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34194 q ha hb
    | true =>
      simp only [d14659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34218 q ha hb
  have h2 (q : Pattern) (ha : d14660 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14661 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14662 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34218 q ha hb
    | true =>
      simp only [d14662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34217 q ha hb
  have h5 (q : Pattern) (ha : d14663 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14664 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14665 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14670 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d14671 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14672 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d14672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro34244 (p : Pattern) (ha : d14678 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14668 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34242 q ha hb
    | true =>
      simp only [d14668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14669 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14673 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34243 q ha hb
    | true =>
      simp only [d14673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14674 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14675 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14676 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14677 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14678 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro34245 (p : Pattern) (ha : d14686 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14673 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34243 q ha hb
    | true =>
      simp only [d14673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14674 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14681 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34219 q ha hb
    | true =>
      simp only [d14681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14682 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14683 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14684 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14685 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14686 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro34246 (p : Pattern) (ha : d14725 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14673 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34243 q ha hb
    | true =>
      simp only [d14673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14674 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14722 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14723 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14724 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14725 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro34247 (p : Pattern) (ha : d125556 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14687 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34244 q ha hb
    | true =>
      simp only [d14687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34245 q ha hb
  have h2 (q : Pattern) (ha : d125552 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d14726 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34246 q ha hb
    | true =>
      simp only [d14726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14727 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125553 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125554 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125555 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125556 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro34248 (p : Pattern) (ha : d125562 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14498 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34210 q ha hb
  have h2 (q : Pattern) (ha : d14499 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d14508 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34210 q ha hb
    | true =>
      simp only [d14508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34213 q ha hb
  have h4 (q : Pattern) (ha : d14509 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14510 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d14510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125540 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34231 q ha hb
    | true =>
      simp only [d125540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34238 q ha hb
  have h7 (q : Pattern) (ha : d14629 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34214 q ha hb
    | true =>
      simp only [d14629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34215 q ha hb
  have h8 (q : Pattern) (ha : d125541 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d125541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d125542 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d125543 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d125547 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34239 q ha hb
  have h12 (q : Pattern) (ha : d14638 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34216 q ha hb
  have h13 (q : Pattern) (ha : d125548 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d125548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d125549 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d125549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d125550 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d125550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d125551 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d125551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d125557 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34247 q ha hb
  have h18 (q : Pattern) (ha : d14743 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34221 q ha hb
  have h19 (q : Pattern) (ha : d125558 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d125558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d125559 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d125559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d125560 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d125560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d125561 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d125561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d125562 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d125562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d125562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro34249 (p : Pattern) (ha : d125568 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125563 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d125563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34248 q ha hb
  have h2 (q : Pattern) (ha : d125564 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d125564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d125565 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d125565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d125566 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d125566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d125567 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d125567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125568 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d125568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
end NetHack.Soko22Hazard87
