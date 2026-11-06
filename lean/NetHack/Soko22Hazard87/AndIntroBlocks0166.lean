import NetHack.Soko22Hazard87.AndIntroBlocks0165
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro41500 (p : Pattern) (ha : d17927 p = 1) (hb : d52650 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17922 q = 1) (hb : d52645 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17922, d52645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41499 q ha hb
    | true =>
      simp only [d17922, d52645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17923 q = 1) (hb : d52646 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17923, d52646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17923, d52646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17924 q = 1) (hb : d52647 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17924, d52647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17924, d52647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17925 q = 1) (hb : d52648 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17925, d52648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17925, d52648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17926 q = 1) (hb : d52649 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17926, d52649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17926, d52649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17927 q = 1) (hb : d52650 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d17927, d52650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17927, d52650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41501 (p : Pattern) (ha : d17820 p = 1) (hb : d127219 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d965 q = 1) (hb : d52584 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d965, d52584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d965, d52584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro122 q ha hb
  have h2 (q : Pattern) (ha : d834 q = 1) (hb : d52511 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d834, d52511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro122 q ha hb
    | true =>
      simp only [d834, d52511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d966 q = 1) (hb : d52585 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d966, d52585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d966, d52585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52512 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d17812 q = 1) (hb : d52586 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17812, d52586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17812, d52586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17813 q = 1) (hb : d52587 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17813, d52587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17813, d52587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16356 q = 1) (hb : d127213 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d16356, d127213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16356, d127213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23290 q ha hb
  have h8 (q : Pattern) (ha : d9587 q = 1) (hb : d101167 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9587, d101167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23290 q ha hb
    | true =>
      simp only [d9587, d101167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16357 q = 1) (hb : d127214 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d16357, d127214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16357, d127214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d101169 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d17814 q = 1) (hb : d127215 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17814, d127215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17814, d127215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d17815 q = 1) (hb : d127216 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17815, d127216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d17815, d127216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d17816 q = 1) (hb : d127217 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17816, d127217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17816, d127217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d14644 q = 1) (hb : d122847 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d14644, d122847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14644, d122847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23291 q ha hb
  have h15 (q : Pattern) (ha : d9597 q = 1) (hb : d101177 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9597, d101177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23291 q ha hb
    | true =>
      simp only [d9597, d101177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d14645 q = 1) (hb : d122848 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d14645, d122848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d14645, d122848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d101179 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d17817 q = 1) (hb : d122849 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17817, d122849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d17817, d122849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d17818 q = 1) (hb : d122850 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17818, d122850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d17818, d122850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d12858 q = 1) (hb : d113214 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12858, d113214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12858, d113214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23273 q ha hb
  have h21 (q : Pattern) (ha : d9468 q = 1) (hb : d101083 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23273 q ha hb
    | true =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d12859 q = 1) (hb : d113215 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12859, d113215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d12859, d113215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d0 q = 1) (hb : d101085 q = 1) : d0 q = 1 := by
    exact ha
  have h24 (q : Pattern) (ha : d17714 q = 1) (hb : d113216 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17714, d113216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d17714, d113216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d17715 q = 1) (hb : d113217 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17715, d113217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d17715, d113217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d17819 q = 1) (hb : d127218 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17819, d127218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d17819, d127218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d17820 q = 1) (hb : d127219 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17820, d127219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d17820, d127219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro41502 (p : Pattern) (ha : d17824 p = 1) (hb : d127220 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d659 q = 1) (hb : d52363 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d659, d52363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d659, d52363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76 q ha hb
  have h2 (q : Pattern) (ha : d543 q = 1) (hb : d52290 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d543, d52290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76 q ha hb
    | true =>
      simp only [d543, d52290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d660 q = 1) (hb : d52364 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d660, d52364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d660, d52364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52291 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d17709 q = 1) (hb : d52365 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17709, d52365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17709, d52365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17710 q = 1) (hb : d52366 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17710, d52366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17710, d52366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16156 q = 1) (hb : d127047 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d16156, d127047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16156, d127047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23272 q ha hb
  have h8 (q : Pattern) (ha : d9458 q = 1) (hb : d101073 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9458, d101073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23272 q ha hb
    | true =>
      simp only [d9458, d101073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16157 q = 1) (hb : d127048 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d16157, d127048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16157, d127048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d101075 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d17711 q = 1) (hb : d127049 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17711, d127049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17711, d127049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d17712 q = 1) (hb : d127050 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17712, d127050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d17712, d127050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d17713 q = 1) (hb : d127051 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17713, d127051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17713, d127051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d12858 q = 1) (hb : d113214 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12858, d113214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12858, d113214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23273 q ha hb
  have h15 (q : Pattern) (ha : d9468 q = 1) (hb : d101083 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23273 q ha hb
    | true =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d12859 q = 1) (hb : d113215 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12859, d113215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d12859, d113215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d101085 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d17714 q = 1) (hb : d113216 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17714, d113216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d17714, d113216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d17715 q = 1) (hb : d113217 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17715, d113217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d17715, d113217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d971 q = 1) (hb : d52590 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d52590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d971, d52590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100 q ha hb
  have h21 (q : Pattern) (ha : d751 q = 1) (hb : d52428 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100 q ha hb
    | true =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d972 q = 1) (hb : d52591 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d52591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d972, d52591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d0 q = 1) (hb : d52429 q = 1) : d0 q = 1 := by
    exact ha
  have h24 (q : Pattern) (ha : d17821 q = 1) (hb : d52592 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17821, d52592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d17821, d52592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d17822 q = 1) (hb : d52593 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17822, d52593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d17822, d52593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d17823 q = 1) (hb : d113218 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17823, d113218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d17823, d113218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d17824 q = 1) (hb : d127220 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17824, d127220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d17824, d127220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro41503 (p : Pattern) (ha : d17829 p = 1) (hb : d127224 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12858 q = 1) (hb : d113214 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12858, d113214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12858, d113214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23273 q ha hb
  have h2 (q : Pattern) (ha : d9468 q = 1) (hb : d101083 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23273 q ha hb
    | true =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12859 q = 1) (hb : d113215 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12859, d113215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12859, d113215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d101085 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d17714 q = 1) (hb : d113216 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17714, d113216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17714, d113216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17715 q = 1) (hb : d113217 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17715, d113217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17715, d113217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d971 q = 1) (hb : d52590 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d52590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d971, d52590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100 q ha hb
  have h8 (q : Pattern) (ha : d751 q = 1) (hb : d52428 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100 q ha hb
    | true =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d972 q = 1) (hb : d52591 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d52591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d972, d52591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52429 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d17821 q = 1) (hb : d52592 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17821, d52592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17821, d52592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d17822 q = 1) (hb : d52593 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17822, d52593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d17822, d52593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d17823 q = 1) (hb : d113218 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17823, d113218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17823, d113218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d17828 q = 1) (hb : d52599 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17828, d52599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d17828, d52599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d17829 q = 1) (hb : d127224 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17829, d127224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d17829, d127224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro41504 (p : Pattern) (ha : d17845 p = 1) (hb : d127234 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17825 q = 1) (hb : d127221 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17825, d127221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41501 q ha hb
    | true =>
      simp only [d17825, d127221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41502 q ha hb
  have h2 (q : Pattern) (ha : d17826 q = 1) (hb : d127222 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17826, d127222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17826, d127222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17827 q = 1) (hb : d127223 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17827, d127223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17827, d127223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17830 q = 1) (hb : d127225 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17830, d127225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41502 q ha hb
    | true =>
      simp only [d17830, d127225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41503 q ha hb
  have h5 (q : Pattern) (ha : d17831 q = 1) (hb : d127226 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17831, d127226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17831, d127226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17832 q = 1) (hb : d127227 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17832, d127227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17832, d127227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17833 q = 1) (hb : d127228 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17833, d127228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17833, d127228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17836 q = 1) (hb : d127229 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17836, d127229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41502 q ha hb
    | true =>
      simp only [d17836, d127229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41496 q ha hb
  have h9 (q : Pattern) (ha : d17837 q = 1) (hb : d127230 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17837, d127230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17837, d127230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17838 q = 1) (hb : d127231 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17838, d127231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17838, d127231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17840 q = 1) (hb : d52606 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17840, d52606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41496 q ha hb
    | true =>
      simp only [d17840, d52606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41497 q ha hb
  have h12 (q : Pattern) (ha : d17841 q = 1) (hb : d52607 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17841, d52607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17841, d52607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d17842 q = 1) (hb : d52608 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17842, d52608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17842, d52608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d17843 q = 1) (hb : d127232 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17843, d127232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17843, d127232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d17844 q = 1) (hb : d127233 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17844, d127233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17844, d127233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d17845 q = 1) (hb : d127234 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17845, d127234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d17845, d127234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro41505 (p : Pattern) (ha : d17850 p = 1) (hb : d127238 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17836 q = 1) (hb : d127229 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17836, d127229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41502 q ha hb
    | true =>
      simp only [d17836, d127229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41496 q ha hb
  have h2 (q : Pattern) (ha : d17837 q = 1) (hb : d127230 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17837, d127230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17837, d127230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17838 q = 1) (hb : d127231 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17838, d127231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17838, d127231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17840 q = 1) (hb : d52606 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17840, d52606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41496 q ha hb
    | true =>
      simp only [d17840, d52606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41497 q ha hb
  have h5 (q : Pattern) (ha : d17841 q = 1) (hb : d52607 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17841, d52607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17841, d52607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17842 q = 1) (hb : d52608 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17842, d52608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17842, d52608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17843 q = 1) (hb : d127232 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17843, d127232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17843, d127232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17848 q = 1) (hb : d52614 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17848, d52614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17848, d52614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17849 q = 1) (hb : d127237 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17849, d127237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17849, d127237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17850 q = 1) (hb : d127238 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17850, d127238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17850, d127238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro41506 (p : Pattern) (ha : d17856 p = 1) (hb : d127244 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17846 q = 1) (hb : d127235 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17846, d127235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41504 q ha hb
    | true =>
      simp only [d17846, d127235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17847 q = 1) (hb : d127236 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17847, d127236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17847, d127236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17851 q = 1) (hb : d127239 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17851, d127239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41505 q ha hb
    | true =>
      simp only [d17851, d127239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17852 q = 1) (hb : d127240 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17852, d127240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17852, d127240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17853 q = 1) (hb : d127241 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17853, d127241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17853, d127241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17854 q = 1) (hb : d127242 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17854, d127242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17854, d127242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17855 q = 1) (hb : d127243 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17855, d127243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17855, d127243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17856 q = 1) (hb : d127244 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17856, d127244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17856, d127244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro41507 (p : Pattern) (ha : d17864 p = 1) (hb : d127248 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17851 q = 1) (hb : d127239 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17851, d127239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41505 q ha hb
    | true =>
      simp only [d17851, d127239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17852 q = 1) (hb : d127240 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17852, d127240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17852, d127240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17859 q = 1) (hb : d52625 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17859, d52625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41498 q ha hb
    | true =>
      simp only [d17859, d52625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17860 q = 1) (hb : d52626 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17860, d52626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17860, d52626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17861 q = 1) (hb : d127245 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17861, d127245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17861, d127245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17862 q = 1) (hb : d127246 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17862, d127246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17862, d127246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17863 q = 1) (hb : d127247 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17863, d127247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17863, d127247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17864 q = 1) (hb : d127248 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17864, d127248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17864, d127248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro41508 (p : Pattern) (ha : d17910 p = 1) (hb : d127255 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17851 q = 1) (hb : d127239 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17851, d127239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41505 q ha hb
    | true =>
      simp only [d17851, d127239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17852 q = 1) (hb : d127240 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17852, d127240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17852, d127240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17907 q = 1) (hb : d127252 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17907, d127252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17907, d127252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17908 q = 1) (hb : d127253 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17908, d127253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17908, d127253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17909 q = 1) (hb : d127254 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17909, d127254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17909, d127254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17910 q = 1) (hb : d127255 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17910, d127255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17910, d127255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41509 (p : Pattern) (ha : d127261 p = 1) (hb : d129350 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17865 q = 1) (hb : d127249 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17865, d127249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41506 q ha hb
    | true =>
      simp only [d17865, d127249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41507 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d127250 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d127251 q = 1) (hb : d129346 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d127251, d129346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127251, d129346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d17911 q = 1) (hb : d127256 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17911, d127256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41508 q ha hb
    | true =>
      simp only [d17911, d127256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17912 q = 1) (hb : d127257 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17912, d127257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17912, d127257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d127258 q = 1) (hb : d129347 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d127258, d129347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d127258, d129347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d127259 q = 1) (hb : d129348 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d127259, d129348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127259, d129348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d127260 q = 1) (hb : d129349 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d127260, d129349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127260, d129349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d127261 q = 1) (hb : d129350 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d127261, d129350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127261, d129350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro41510 (p : Pattern) (ha : d127267 p = 1) (hb : d129356 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d127212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d127262 q = 1) (hb : d129351 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d127262, d129351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127262, d129351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41509 q ha hb
  have h3 (q : Pattern) (ha : d17928 q = 1) (hb : d52651 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d17928, d52651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17928, d52651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41500 q ha hb
  have h4 (q : Pattern) (ha : d127263 q = 1) (hb : d129352 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d127263, d129352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d127263, d129352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d127264 q = 1) (hb : d129353 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d127264, d129353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d127264, d129353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d127265 q = 1) (hb : d129354 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d127265, d129354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d127265, d129354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d127266 q = 1) (hb : d129355 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d127266, d129355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d127266, d129355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d127267 q = 1) (hb : d129356 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d127267, d129356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127267, d129356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41511 (p : Pattern) (ha : d127273 p = 1) (hb : d129362 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127268 q = 1) (hb : d129357 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d127268, d129357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127268, d129357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41510 q ha hb
  have h2 (q : Pattern) (ha : d127269 q = 1) (hb : d129358 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d127269, d129358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127269, d129358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127270 q = 1) (hb : d129359 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d127270, d129359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127270, d129359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d127271 q = 1) (hb : d129360 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d127271, d129360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127271, d129360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d127272 q = 1) (hb : d129361 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d127272, d129361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127272, d129361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d127273 q = 1) (hb : d129362 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d127273, d129362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127273, d129362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41512 (p : Pattern) (ha : d17979 p = 1) (hb : d127473 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1385 q = 1) (hb : d52873 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1385, d52873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1385, d52873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro150 q ha hb
  have h2 (q : Pattern) (ha : d1110 q = 1) (hb : d52691 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1110, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro150 q ha hb
    | true =>
      simp only [d1110, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1386 q = 1) (hb : d52874 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1386, d52874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1386, d52874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52692 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d17974 q = 1) (hb : d52875 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17974, d52875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17974, d52875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17975 q = 1) (hb : d52876 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17975, d52876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17975, d52876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1391 q = 1) (hb : d52879 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1391, d52879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1391, d52879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro151 q ha hb
  have h8 (q : Pattern) (ha : d1121 q = 1) (hb : d52702 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro151 q ha hb
    | true =>
      simp only [d1121, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1392 q = 1) (hb : d52880 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1392, d52880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1392, d52880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52703 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d17976 q = 1) (hb : d52881 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17976, d52881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17976, d52881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d17977 q = 1) (hb : d52882 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17977, d52882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d17977, d52882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d17978 q = 1) (hb : d52883 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17978, d52883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17978, d52883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d15004 q = 1) (hb : d123129 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15004, d123129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15004, d123129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23303 q ha hb
  have h15 (q : Pattern) (ha : d9800 q = 1) (hb : d101321 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9800, d101321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23303 q ha hb
    | true =>
      simp only [d9800, d101321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d15005 q = 1) (hb : d123130 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15005, d123130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d15005, d123130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d101323 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d17958 q = 1) (hb : d123131 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17958, d123131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d17958, d123131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d17959 q = 1) (hb : d123132 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17959, d123132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d17959, d123132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d17968 q = 1) (hb : d123133 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17968, d123133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d17968, d123133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d17979 q = 1) (hb : d127473 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17979, d127473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d17979, d127473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro41513 (p : Pattern) (ha : d18008 p = 1) (hb : d123167 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1391 q = 1) (hb : d52879 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1391, d52879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1391, d52879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro151 q ha hb
  have h2 (q : Pattern) (ha : d1121 q = 1) (hb : d52702 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro151 q ha hb
    | true =>
      simp only [d1121, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1392 q = 1) (hb : d52880 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1392, d52880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1392, d52880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52703 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d17976 q = 1) (hb : d52881 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17976, d52881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17976, d52881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17977 q = 1) (hb : d52882 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17977, d52882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17977, d52882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d18007 q = 1) (hb : d52888 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18007, d52888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18007, d52888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15019 q = 1) (hb : d123144 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15019, d123144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15019, d123144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23305 q ha hb
  have h9 (q : Pattern) (ha : d9844 q = 1) (hb : d101365 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9844, d101365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23305 q ha hb
    | true =>
      simp only [d9844, d101365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15020 q = 1) (hb : d123145 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15020, d123145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15020, d123145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d101367 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d17986 q = 1) (hb : d123146 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17986, d123146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17986, d123146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d17987 q = 1) (hb : d123147 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17987, d123147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d17987, d123147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d17988 q = 1) (hb : d123148 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17988, d123148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d17988, d123148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d18008 q = 1) (hb : d123167 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18008, d123167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18008, d123167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro41514 (p : Pattern) (ha : d18014 p = 1) (hb : d127499 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18009 q = 1) (hb : d127494 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18009, d127494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41512 q ha hb
    | true =>
      simp only [d18009, d127494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41513 q ha hb
  have h2 (q : Pattern) (ha : d18010 q = 1) (hb : d127495 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18010, d127495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18010, d127495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18011 q = 1) (hb : d127496 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18011, d127496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18011, d127496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18012 q = 1) (hb : d127497 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18012, d127497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18012, d127497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18013 q = 1) (hb : d127498 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18013, d127498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18013, d127498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18014 q = 1) (hb : d127499 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18014, d127499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18014, d127499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41515 (p : Pattern) (ha : d18101 p = 1) (hb : d127518 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18015 q = 1) (hb : d127500 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18015, d127500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41514 q ha hb
    | true =>
      simp only [d18015, d127500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18016 q = 1) (hb : d127501 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18016, d127501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18016, d127501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18098 q = 1) (hb : d127515 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18098, d127515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18098, d127515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18099 q = 1) (hb : d127516 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18099, d127516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18099, d127516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18100 q = 1) (hb : d127517 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18100, d127517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18100, d127517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18101 q = 1) (hb : d127518 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18101, d127518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18101, d127518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41516 (p : Pattern) (ha : d18107 p = 1) (hb : d127545 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18102 q = 1) (hb : d127540 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18102, d127540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41515 q ha hb
    | true =>
      simp only [d18102, d127540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18103 q = 1) (hb : d127541 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d18103, d127541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18103, d127541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18104 q = 1) (hb : d127542 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d18104, d127542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18104, d127542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18105 q = 1) (hb : d127543 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d18105, d127543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18105, d127543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18106 q = 1) (hb : d127544 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d18106, d127544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18106, d127544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18107 q = 1) (hb : d127545 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d18107, d127545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18107, d127545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41517 (p : Pattern) (ha : d17952 p = 1) (hb : d127456 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1376 q = 1) (hb : d52864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1376, d52864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1376, d52864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro174 q ha hb
  have h2 (q : Pattern) (ha : d1210 q = 1) (hb : d52791 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1210, d52791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro174 q ha hb
    | true =>
      simp only [d1210, d52791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1377 q = 1) (hb : d52865 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1377, d52865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1377, d52865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52792 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d17942 q = 1) (hb : d52866 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17942, d52866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17942, d52866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17943 q = 1) (hb : d52867 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17943, d52867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17943, d52867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16649 q = 1) (hb : d127450 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d16649, d127450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16649, d127450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23310 q ha hb
  have h8 (q : Pattern) (ha : d9753 q = 1) (hb : d101274 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9753, d101274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23310 q ha hb
    | true =>
      simp only [d9753, d101274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16650 q = 1) (hb : d127451 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d16650, d127451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16650, d127451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d101276 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d17944 q = 1) (hb : d127452 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17944, d127452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17944, d127452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d17945 q = 1) (hb : d127453 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17945, d127453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d17945, d127453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d17946 q = 1) (hb : d127454 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17946, d127454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17946, d127454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d14987 q = 1) (hb : d123112 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d14987, d123112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14987, d123112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23311 q ha hb
  have h15 (q : Pattern) (ha : d9763 q = 1) (hb : d101284 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9763, d101284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23311 q ha hb
    | true =>
      simp only [d9763, d101284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d14988 q = 1) (hb : d123113 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d14988, d123113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d14988, d123113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d101286 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d17947 q = 1) (hb : d123114 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17947, d123114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d17947, d123114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d17948 q = 1) (hb : d123115 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17948, d123115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d17948, d123115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d14994 q = 1) (hb : d123119 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d14994, d123119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14994, d123119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23313 q ha hb
  have h21 (q : Pattern) (ha : d9778 q = 1) (hb : d101299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9778, d101299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23313 q ha hb
    | true =>
      simp only [d9778, d101299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d14995 q = 1) (hb : d123120 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d14995, d123120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d14995, d123120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d0 q = 1) (hb : d101301 q = 1) : d0 q = 1 := by
    exact ha
  have h24 (q : Pattern) (ha : d17949 q = 1) (hb : d123121 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17949, d123121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d17949, d123121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d17950 q = 1) (hb : d123122 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17950, d123122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d17950, d123122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d17951 q = 1) (hb : d127455 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17951, d127455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d17951, d127455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d17952 q = 1) (hb : d127456 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17952, d127456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d17952, d127456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro41518 (p : Pattern) (ha : d17961 p = 1) (hb : d127463 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1380 q = 1) (hb : d52868 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1380, d52868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1380, d52868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro149 q ha hb
  have h2 (q : Pattern) (ha : d1100 q = 1) (hb : d52681 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1100, d52681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro149 q ha hb
    | true =>
      simp only [d1100, d52681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1381 q = 1) (hb : d52869 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1381, d52869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1381, d52869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52682 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d17953 q = 1) (hb : d52870 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17953, d52870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17953, d52870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17954 q = 1) (hb : d52871 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17954, d52871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17954, d52871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16656 q = 1) (hb : d127457 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d16656, d127457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16656, d127457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23315 q ha hb
  have h8 (q : Pattern) (ha : d9789 q = 1) (hb : d101310 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9789, d101310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23315 q ha hb
    | true =>
      simp only [d9789, d101310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16657 q = 1) (hb : d127458 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d16657, d127458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16657, d127458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d101312 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d17955 q = 1) (hb : d127459 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17955, d127459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17955, d127459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d17956 q = 1) (hb : d127460 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17956, d127460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d17956, d127460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d17957 q = 1) (hb : d127461 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17957, d127461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17957, d127461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d14994 q = 1) (hb : d123119 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d14994, d123119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14994, d123119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23313 q ha hb
  have h15 (q : Pattern) (ha : d9778 q = 1) (hb : d101299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9778, d101299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23313 q ha hb
    | true =>
      simp only [d9778, d101299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d14995 q = 1) (hb : d123120 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d14995, d123120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d14995, d123120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d101301 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d17949 q = 1) (hb : d123121 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17949, d123121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d17949, d123121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d17950 q = 1) (hb : d123122 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17950, d123122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d17950, d123122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d15004 q = 1) (hb : d123129 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15004, d123129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15004, d123129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23303 q ha hb
  have h21 (q : Pattern) (ha : d9800 q = 1) (hb : d101321 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9800, d101321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23303 q ha hb
    | true =>
      simp only [d9800, d101321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d15005 q = 1) (hb : d123130 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15005, d123130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d15005, d123130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d0 q = 1) (hb : d101323 q = 1) : d0 q = 1 := by
    exact ha
  have h24 (q : Pattern) (ha : d17958 q = 1) (hb : d123131 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17958, d123131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d17958, d123131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d17959 q = 1) (hb : d123132 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17959, d123132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d17959, d123132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d17960 q = 1) (hb : d127462 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17960, d127462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d17960, d127462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d17961 q = 1) (hb : d127463 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17961, d127463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d17961, d127463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro41519 (p : Pattern) (ha : d17969 p = 1) (hb : d127468 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13160 q = 1) (hb : d113452 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13160, d113452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13160, d113452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23317 q ha hb
  have h2 (q : Pattern) (ha : d9814 q = 1) (hb : d101335 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9814, d101335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23317 q ha hb
    | true =>
      simp only [d9814, d101335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13161 q = 1) (hb : d113453 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13161, d113453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13161, d113453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d101337 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d17965 q = 1) (hb : d113454 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17965, d113454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17965, d113454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17966 q = 1) (hb : d113455 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17966, d113455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17966, d113455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15004 q = 1) (hb : d123129 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15004, d123129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15004, d123129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23303 q ha hb
  have h8 (q : Pattern) (ha : d9800 q = 1) (hb : d101321 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9800, d101321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23303 q ha hb
    | true =>
      simp only [d9800, d101321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d15005 q = 1) (hb : d123130 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15005, d123130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15005, d123130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d101323 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d17958 q = 1) (hb : d123131 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17958, d123131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17958, d123131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d17959 q = 1) (hb : d123132 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17959, d123132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d17959, d123132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d17967 q = 1) (hb : d127467 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17967, d127467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17967, d127467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d17968 q = 1) (hb : d123133 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17968, d123133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d17968, d123133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d17969 q = 1) (hb : d127468 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17969, d127468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d17969, d127468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro41520 (p : Pattern) (ha : d17989 p = 1) (hb : d123149 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6350 q = 1) (hb : d76090 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d6350, d76090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6350, d76090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7947 q ha hb
  have h2 (q : Pattern) (ha : d5018 q = 1) (hb : d69108 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5018, d69108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7947 q ha hb
    | true =>
      simp only [d5018, d69108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6351 q = 1) (hb : d76091 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d6351, d76091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6351, d76091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d69109 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d17983 q = 1) (hb : d76092 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17983, d76092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17983, d76092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17984 q = 1) (hb : d76093 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17984, d76093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17984, d76093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17985 q = 1) (hb : d76094 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17985, d76094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17985, d76094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15019 q = 1) (hb : d123144 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15019, d123144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15019, d123144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23305 q ha hb
  have h9 (q : Pattern) (ha : d9844 q = 1) (hb : d101365 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9844, d101365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23305 q ha hb
    | true =>
      simp only [d9844, d101365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15020 q = 1) (hb : d123145 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15020, d123145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15020, d123145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d101367 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d17986 q = 1) (hb : d123146 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17986, d123146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17986, d123146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d17987 q = 1) (hb : d123147 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17987, d123147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d17987, d123147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d17988 q = 1) (hb : d123148 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17988, d123148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d17988, d123148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d17989 q = 1) (hb : d123149 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17989, d123149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17989, d123149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro41521 (p : Pattern) (ha : d17995 p = 1) (hb : d127482 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17962 q = 1) (hb : d127464 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17962, d127464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41517 q ha hb
    | true =>
      simp only [d17962, d127464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41518 q ha hb
  have h2 (q : Pattern) (ha : d17963 q = 1) (hb : d127465 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17963, d127465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17963, d127465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17964 q = 1) (hb : d127466 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17964, d127466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17964, d127466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17970 q = 1) (hb : d127469 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17970, d127469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41518 q ha hb
    | true =>
      simp only [d17970, d127469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41519 q ha hb
  have h5 (q : Pattern) (ha : d17971 q = 1) (hb : d127470 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17971, d127470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17971, d127470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17972 q = 1) (hb : d127471 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17972, d127471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17972, d127471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17973 q = 1) (hb : d127472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17973, d127472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17973, d127472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17980 q = 1) (hb : d127474 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17980, d127474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41518 q ha hb
    | true =>
      simp only [d17980, d127474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41512 q ha hb
  have h9 (q : Pattern) (ha : d17981 q = 1) (hb : d127475 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17981, d127475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17981, d127475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17982 q = 1) (hb : d127476 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17982, d127476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17982, d127476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17990 q = 1) (hb : d127477 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17990, d127477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41512 q ha hb
    | true =>
      simp only [d17990, d127477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41520 q ha hb
  have h12 (q : Pattern) (ha : d17991 q = 1) (hb : d127478 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17991, d127478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17991, d127478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d17992 q = 1) (hb : d127479 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17992, d127479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17992, d127479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d17993 q = 1) (hb : d127480 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17993, d127480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17993, d127480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d17994 q = 1) (hb : d127481 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17994, d127481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17994, d127481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d17995 q = 1) (hb : d127482 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17995, d127482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d17995, d127482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro41522 (p : Pattern) (ha : d18000 p = 1) (hb : d127487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17980 q = 1) (hb : d127474 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17980, d127474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41518 q ha hb
    | true =>
      simp only [d17980, d127474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41512 q ha hb
  have h2 (q : Pattern) (ha : d17981 q = 1) (hb : d127475 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17981, d127475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17981, d127475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17982 q = 1) (hb : d127476 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17982, d127476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17982, d127476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17990 q = 1) (hb : d127477 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17990, d127477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41512 q ha hb
    | true =>
      simp only [d17990, d127477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41520 q ha hb
  have h5 (q : Pattern) (ha : d17991 q = 1) (hb : d127478 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17991, d127478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17991, d127478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17992 q = 1) (hb : d127479 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17992, d127479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17992, d127479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17993 q = 1) (hb : d127480 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17993, d127480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17993, d127480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17998 q = 1) (hb : d127485 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17998, d127485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17998, d127485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17999 q = 1) (hb : d127486 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17999, d127486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17999, d127486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18000 q = 1) (hb : d127487 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18000, d127487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d18000, d127487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro41523 (p : Pattern) (ha : d18006 p = 1) (hb : d127493 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17996 q = 1) (hb : d127483 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17996, d127483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41521 q ha hb
    | true =>
      simp only [d17996, d127483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17997 q = 1) (hb : d127484 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17997, d127484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17997, d127484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18001 q = 1) (hb : d127488 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18001, d127488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41522 q ha hb
    | true =>
      simp only [d18001, d127488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18002 q = 1) (hb : d127489 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18002, d127489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18002, d127489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18003 q = 1) (hb : d127490 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18003, d127490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18003, d127490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18004 q = 1) (hb : d127491 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18004, d127491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18004, d127491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d18005 q = 1) (hb : d127492 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18005, d127492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18005, d127492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d18006 q = 1) (hb : d127493 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18006, d127493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18006, d127493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro41524 (p : Pattern) (ha : d18020 p = 1) (hb : d127505 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18001 q = 1) (hb : d127488 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18001, d127488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41522 q ha hb
    | true =>
      simp only [d18001, d127488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18002 q = 1) (hb : d127489 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18002, d127489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18002, d127489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18015 q = 1) (hb : d127500 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18015, d127500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41514 q ha hb
    | true =>
      simp only [d18015, d127500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18016 q = 1) (hb : d127501 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18016, d127501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18016, d127501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18017 q = 1) (hb : d127502 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18017, d127502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18017, d127502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18018 q = 1) (hb : d127503 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18018, d127503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18018, d127503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d18019 q = 1) (hb : d127504 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18019, d127504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18019, d127504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d18020 q = 1) (hb : d127505 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18020, d127505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18020, d127505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro41525 (p : Pattern) (ha : d18078 p = 1) (hb : d113482 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1391 q = 1) (hb : d52879 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1391, d52879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1391, d52879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro151 q ha hb
  have h2 (q : Pattern) (ha : d1121 q = 1) (hb : d52702 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro151 q ha hb
    | true =>
      simp only [d1121, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1392 q = 1) (hb : d52880 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1392, d52880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1392, d52880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52703 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d17976 q = 1) (hb : d52881 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17976, d52881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17976, d52881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17977 q = 1) (hb : d52882 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17977, d52882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17977, d52882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d18007 q = 1) (hb : d52888 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18007, d52888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18007, d52888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d18078 q = 1) (hb : d113482 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18078, d113482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18078, d113482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro41526 (p : Pattern) (ha : d18084 p = 1) (hb : d127526 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17980 q = 1) (hb : d127474 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17980, d127474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41518 q ha hb
    | true =>
      simp only [d17980, d127474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41512 q ha hb
  have h2 (q : Pattern) (ha : d17981 q = 1) (hb : d127475 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17981, d127475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17981, d127475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17982 q = 1) (hb : d127476 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17982, d127476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17982, d127476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17990 q = 1) (hb : d127477 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17990, d127477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41512 q ha hb
    | true =>
      simp only [d17990, d127477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41520 q ha hb
  have h5 (q : Pattern) (ha : d17991 q = 1) (hb : d127478 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17991, d127478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17991, d127478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17992 q = 1) (hb : d127479 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17992, d127479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17992, d127479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17993 q = 1) (hb : d127480 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17993, d127480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17993, d127480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18079 q = 1) (hb : d127521 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18079, d127521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41512 q ha hb
    | true =>
      simp only [d18079, d127521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41525 q ha hb
  have h9 (q : Pattern) (ha : d18080 q = 1) (hb : d127522 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18080, d127522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18080, d127522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18081 q = 1) (hb : d127523 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18081, d127523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18081, d127523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d18082 q = 1) (hb : d127524 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18082, d127524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18082, d127524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d18083 q = 1) (hb : d127525 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18083, d127525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18083, d127525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d18084 q = 1) (hb : d127526 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18084, d127526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d18084, d127526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro41527 (p : Pattern) (ha : d18090 p = 1) (hb : d127532 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18085 q = 1) (hb : d127527 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18085, d127527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41526 q ha hb
    | true =>
      simp only [d18085, d127527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18086 q = 1) (hb : d127528 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18086, d127528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18086, d127528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18087 q = 1) (hb : d127529 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18087, d127529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18087, d127529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18088 q = 1) (hb : d127530 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18088, d127530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18088, d127530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18089 q = 1) (hb : d127531 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18089, d127531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18089, d127531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18090 q = 1) (hb : d127532 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18090, d127532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18090, d127532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41528 (p : Pattern) (ha : d127538 p = 1) (hb : d129369 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18021 q = 1) (hb : d127506 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18021, d127506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41523 q ha hb
    | true =>
      simp only [d18021, d127506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41524 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d127519 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d127520 q = 1) (hb : d129365 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d127520, d129365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127520, d129365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d18091 q = 1) (hb : d127533 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18091, d127533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41527 q ha hb
    | true =>
      simp only [d18091, d127533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18092 q = 1) (hb : d127534 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d18092, d127534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18092, d127534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d127535 q = 1) (hb : d129366 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d127535, d129366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d127535, d129366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d127536 q = 1) (hb : d129367 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d127536, d129367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127536, d129367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d127537 q = 1) (hb : d129368 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d127537, d129368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127537, d129368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d127538 q = 1) (hb : d129369 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d127538, d129369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127538, d129369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro41529 (p : Pattern) (ha : d127551 p = 1) (hb : d129375 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d127449 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d127539 q = 1) (hb : d129370 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d127539, d129370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127539, d129370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41528 q ha hb
  have h3 (q : Pattern) (ha : d18108 q = 1) (hb : d127546 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d18108, d127546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18108, d127546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41516 q ha hb
  have h4 (q : Pattern) (ha : d127547 q = 1) (hb : d129371 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d127547, d129371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d127547, d129371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d127548 q = 1) (hb : d129372 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d127548, d129372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d127548, d129372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d127549 q = 1) (hb : d129373 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d127549, d129373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d127549, d129373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d127550 q = 1) (hb : d129374 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d127550, d129374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d127550, d129374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d127551 q = 1) (hb : d129375 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d127551, d129375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127551, d129375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41530 (p : Pattern) (ha : d127557 p = 1) (hb : d129381 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127552 q = 1) (hb : d129376 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d127552, d129376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127552, d129376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41529 q ha hb
  have h2 (q : Pattern) (ha : d127553 q = 1) (hb : d129377 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d127553, d129377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127553, d129377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127554 q = 1) (hb : d129378 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d127554, d129378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127554, d129378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d127555 q = 1) (hb : d129379 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d127555, d129379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127555, d129379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d127556 q = 1) (hb : d129380 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d127556, d129380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127556, d129380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d127557 q = 1) (hb : d129381 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d127557, d129381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127557, d129381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41531 (p : Pattern) (ha : d18160 p = 1) (hb : d127766 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1862 q = 1) (hb : d53188 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1862, d53188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1862, d53188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro208 q ha hb
  have h2 (q : Pattern) (ha : d1570 q = 1) (hb : d53011 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1570, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro208 q ha hb
    | true =>
      simp only [d1570, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1863 q = 1) (hb : d53189 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1863, d53189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1863, d53189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53012 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d18155 q = 1) (hb : d53190 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18155, d53190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18155, d53190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18156 q = 1) (hb : d53191 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18156, d53191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18156, d53191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17027 q = 1) (hb : d127761 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17027, d127761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17027, d127761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23331 q ha hb
  have h8 (q : Pattern) (ha : d10115 q = 1) (hb : d101542 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10115, d101542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23331 q ha hb
    | true =>
      simp only [d10115, d101542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17028 q = 1) (hb : d127762 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17028, d127762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17028, d127762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d101544 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d18157 q = 1) (hb : d127763 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18157, d127763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d18157, d127763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d18158 q = 1) (hb : d127764 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18158, d127764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d18158, d127764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d18159 q = 1) (hb : d127765 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18159, d127765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18159, d127765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d15397 q = 1) (hb : d123436 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15397, d123436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15397, d123436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23330 q ha hb
  have h15 (q : Pattern) (ha : d10085 q = 1) (hb : d101512 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10085, d101512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23330 q ha hb
    | true =>
      simp only [d10085, d101512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d15398 q = 1) (hb : d123437 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15398, d123437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d15398, d123437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d101514 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d18139 q = 1) (hb : d123438 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18139, d123438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d18139, d123438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d18140 q = 1) (hb : d123439 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18140, d123439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d18140, d123439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d18149 q = 1) (hb : d123440 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18149, d123440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d18149, d123440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d18160 q = 1) (hb : d127766 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18160, d127766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d18160, d127766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro41532 (p : Pattern) (ha : d18191 p = 1) (hb : d123474 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1868 q = 1) (hb : d53194 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1868, d53194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1868, d53194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro209 q ha hb
  have h2 (q : Pattern) (ha : d1582 q = 1) (hb : d53023 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1582, d53023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro209 q ha hb
    | true =>
      simp only [d1582, d53023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1869 q = 1) (hb : d53195 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1869, d53195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1869, d53195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53024 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d18188 q = 1) (hb : d53196 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18188, d53196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18188, d53196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18189 q = 1) (hb : d53197 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18189, d53197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18189, d53197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d18190 q = 1) (hb : d53203 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18190, d53203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18190, d53203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15412 q = 1) (hb : d123451 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15412, d123451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15412, d123451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23333 q ha hb
  have h9 (q : Pattern) (ha : d10135 q = 1) (hb : d101562 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10135, d101562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23333 q ha hb
    | true =>
      simp only [d10135, d101562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15413 q = 1) (hb : d123452 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15413, d123452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15413, d123452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d101564 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d18167 q = 1) (hb : d123453 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18167, d123453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18167, d123453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d18168 q = 1) (hb : d123454 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18168, d123454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d18168, d123454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d18169 q = 1) (hb : d123455 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18169, d123455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d18169, d123455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d18191 q = 1) (hb : d123474 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18191, d123474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18191, d123474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro41533 (p : Pattern) (ha : d18197 p = 1) (hb : d127792 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18192 q = 1) (hb : d127787 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18192, d127787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41531 q ha hb
    | true =>
      simp only [d18192, d127787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41532 q ha hb
  have h2 (q : Pattern) (ha : d18193 q = 1) (hb : d127788 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18193, d127788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18193, d127788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18194 q = 1) (hb : d127789 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18194, d127789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18194, d127789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18195 q = 1) (hb : d127790 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18195, d127790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18195, d127790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18196 q = 1) (hb : d127791 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18196, d127791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18196, d127791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18197 q = 1) (hb : d127792 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18197, d127792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18197, d127792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41534 (p : Pattern) (ha : d18286 p = 1) (hb : d127811 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18198 q = 1) (hb : d127793 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18198, d127793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41533 q ha hb
    | true =>
      simp only [d18198, d127793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18199 q = 1) (hb : d127794 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18199, d127794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18199, d127794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18283 q = 1) (hb : d127808 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18283, d127808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18283, d127808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18284 q = 1) (hb : d127809 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18284, d127809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18284, d127809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18285 q = 1) (hb : d127810 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18285, d127810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18285, d127810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18286 q = 1) (hb : d127811 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18286, d127811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18286, d127811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41535 (p : Pattern) (ha : d18292 p = 1) (hb : d127838 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18287 q = 1) (hb : d127833 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18287, d127833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41534 q ha hb
    | true =>
      simp only [d18287, d127833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18288 q = 1) (hb : d127834 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d18288, d127834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18288, d127834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18289 q = 1) (hb : d127835 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d18289, d127835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18289, d127835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18290 q = 1) (hb : d127836 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d18290, d127836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18290, d127836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18291 q = 1) (hb : d127837 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d18291, d127837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18291, d127837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18292 q = 1) (hb : d127838 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d18292, d127838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18292, d127838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41536 (p : Pattern) (ha : d18133 p = 1) (hb : d127744 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1853 q = 1) (hb : d53179 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1853, d53179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1853, d53179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro230 q ha hb
  have h2 (q : Pattern) (ha : d1665 q = 1) (hb : d53106 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1665, d53106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro230 q ha hb
    | true =>
      simp only [d1665, d53106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1854 q = 1) (hb : d53180 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1854, d53180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1854, d53180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53107 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d18123 q = 1) (hb : d53181 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18123, d53181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18123, d53181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18124 q = 1) (hb : d53182 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18124, d53182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18124, d53182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17004 q = 1) (hb : d127738 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17004, d127738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17004, d127738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23338 q ha hb
  have h8 (q : Pattern) (ha : d10036 q = 1) (hb : d101463 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10036, d101463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23338 q ha hb
    | true =>
      simp only [d10036, d101463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17005 q = 1) (hb : d127739 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17005, d127739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17005, d127739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d101465 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d18125 q = 1) (hb : d127740 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18125, d127740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d18125, d127740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d18126 q = 1) (hb : d127741 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18126, d127741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d18126, d127741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d18127 q = 1) (hb : d127742 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18127, d127742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18127, d127742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d15380 q = 1) (hb : d123419 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15380, d123419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15380, d123419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23339 q ha hb
  have h15 (q : Pattern) (ha : d10046 q = 1) (hb : d101473 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10046, d101473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23339 q ha hb
    | true =>
      simp only [d10046, d101473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d15381 q = 1) (hb : d123420 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15381, d123420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d15381, d123420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d101475 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d18128 q = 1) (hb : d123421 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18128, d123421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d18128, d123421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d18129 q = 1) (hb : d123422 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18129, d123422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d18129, d123422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d15387 q = 1) (hb : d123426 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15387, d123426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15387, d123426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23341 q ha hb
  have h21 (q : Pattern) (ha : d10063 q = 1) (hb : d101490 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10063, d101490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23341 q ha hb
    | true =>
      simp only [d10063, d101490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d15388 q = 1) (hb : d123427 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15388, d123427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d15388, d123427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d0 q = 1) (hb : d101492 q = 1) : d0 q = 1 := by
    exact ha
  have h24 (q : Pattern) (ha : d18130 q = 1) (hb : d123428 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18130, d123428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d18130, d123428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d18131 q = 1) (hb : d123429 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18131, d123429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d18131, d123429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d18132 q = 1) (hb : d127743 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18132, d127743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d18132, d127743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d18133 q = 1) (hb : d127744 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18133, d127744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d18133, d127744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro41537 (p : Pattern) (ha : d18142 p = 1) (hb : d127751 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1857 q = 1) (hb : d53183 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1857, d53183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1857, d53183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro205 q ha hb
  have h2 (q : Pattern) (ha : d1555 q = 1) (hb : d52996 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1555, d52996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro205 q ha hb
    | true =>
      simp only [d1555, d52996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1858 q = 1) (hb : d53184 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1858, d53184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1858, d53184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52997 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d18134 q = 1) (hb : d53185 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18134, d53185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18134, d53185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18135 q = 1) (hb : d53186 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18135, d53186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18135, d53186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17011 q = 1) (hb : d127745 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17011, d127745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17011, d127745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23343 q ha hb
  have h8 (q : Pattern) (ha : d10074 q = 1) (hb : d101501 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10074, d101501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23343 q ha hb
    | true =>
      simp only [d10074, d101501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17012 q = 1) (hb : d127746 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17012, d127746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17012, d127746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d101503 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d18136 q = 1) (hb : d127747 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18136, d127747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d18136, d127747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d18137 q = 1) (hb : d127748 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18137, d127748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d18137, d127748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d18138 q = 1) (hb : d127749 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18138, d127749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18138, d127749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d15387 q = 1) (hb : d123426 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15387, d123426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15387, d123426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23341 q ha hb
  have h15 (q : Pattern) (ha : d10063 q = 1) (hb : d101490 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10063, d101490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23341 q ha hb
    | true =>
      simp only [d10063, d101490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d15388 q = 1) (hb : d123427 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15388, d123427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d15388, d123427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d101492 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d18130 q = 1) (hb : d123428 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18130, d123428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d18130, d123428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d18131 q = 1) (hb : d123429 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18131, d123429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d18131, d123429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d15397 q = 1) (hb : d123436 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15397, d123436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15397, d123436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23330 q ha hb
  have h21 (q : Pattern) (ha : d10085 q = 1) (hb : d101512 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10085, d101512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23330 q ha hb
    | true =>
      simp only [d10085, d101512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d15398 q = 1) (hb : d123437 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15398, d123437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d15398, d123437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d0 q = 1) (hb : d101514 q = 1) : d0 q = 1 := by
    exact ha
  have h24 (q : Pattern) (ha : d18139 q = 1) (hb : d123438 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18139, d123438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d18139, d123438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d18140 q = 1) (hb : d123439 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18140, d123439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d18140, d123439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d18141 q = 1) (hb : d127750 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18141, d127750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d18141, d127750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d18142 q = 1) (hb : d127751 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18142, d127751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d18142, d127751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro41538 (p : Pattern) (ha : d18150 p = 1) (hb : d127756 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13486 q = 1) (hb : d113708 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13486, d113708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13486, d113708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23345 q ha hb
  have h2 (q : Pattern) (ha : d10099 q = 1) (hb : d101526 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10099, d101526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23345 q ha hb
    | true =>
      simp only [d10099, d101526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13487 q = 1) (hb : d113709 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13487, d113709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13487, d113709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d101528 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d18146 q = 1) (hb : d113710 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18146, d113710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18146, d113710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18147 q = 1) (hb : d113711 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18147, d113711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18147, d113711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15397 q = 1) (hb : d123436 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15397, d123436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15397, d123436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23330 q ha hb
  have h8 (q : Pattern) (ha : d10085 q = 1) (hb : d101512 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10085, d101512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23330 q ha hb
    | true =>
      simp only [d10085, d101512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d15398 q = 1) (hb : d123437 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15398, d123437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15398, d123437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d101514 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d18139 q = 1) (hb : d123438 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18139, d123438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d18139, d123438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d18140 q = 1) (hb : d123439 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18140, d123439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d18140, d123439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d18148 q = 1) (hb : d127755 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18148, d127755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18148, d127755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d18149 q = 1) (hb : d123440 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18149, d123440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d18149, d123440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d18150 q = 1) (hb : d127756 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18150, d127756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d18150, d127756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro41539 (p : Pattern) (ha : d18170 p = 1) (hb : d123456 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6496 q = 1) (hb : d76225 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d6496, d76225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6496, d76225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7964 q ha hb
  have h2 (q : Pattern) (ha : d5134 q = 1) (hb : d69221 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5134, d69221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7964 q ha hb
    | true =>
      simp only [d5134, d69221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6497 q = 1) (hb : d76226 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d6497, d76226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6497, d76226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d69222 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d18164 q = 1) (hb : d76227 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18164, d76227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18164, d76227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18165 q = 1) (hb : d76228 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18165, d76228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18165, d76228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d18166 q = 1) (hb : d76229 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18166, d76229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18166, d76229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15412 q = 1) (hb : d123451 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15412, d123451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15412, d123451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23333 q ha hb
  have h9 (q : Pattern) (ha : d10135 q = 1) (hb : d101562 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10135, d101562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23333 q ha hb
    | true =>
      simp only [d10135, d101562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15413 q = 1) (hb : d123452 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15413, d123452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15413, d123452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d101564 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d18167 q = 1) (hb : d123453 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18167, d123453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18167, d123453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d18168 q = 1) (hb : d123454 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18168, d123454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d18168, d123454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d18169 q = 1) (hb : d123455 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18169, d123455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d18169, d123455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d18170 q = 1) (hb : d123456 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18170, d123456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18170, d123456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro41540 (p : Pattern) (ha : d18176 p = 1) (hb : d127775 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18143 q = 1) (hb : d127752 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18143, d127752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41536 q ha hb
    | true =>
      simp only [d18143, d127752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41537 q ha hb
  have h2 (q : Pattern) (ha : d18144 q = 1) (hb : d127753 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18144, d127753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18144, d127753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18145 q = 1) (hb : d127754 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18145, d127754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18145, d127754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18151 q = 1) (hb : d127757 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18151, d127757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41537 q ha hb
    | true =>
      simp only [d18151, d127757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41538 q ha hb
  have h5 (q : Pattern) (ha : d18152 q = 1) (hb : d127758 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18152, d127758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18152, d127758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18153 q = 1) (hb : d127759 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18153, d127759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18153, d127759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d18154 q = 1) (hb : d127760 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18154, d127760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18154, d127760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18161 q = 1) (hb : d127767 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18161, d127767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41537 q ha hb
    | true =>
      simp only [d18161, d127767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41531 q ha hb
  have h9 (q : Pattern) (ha : d18162 q = 1) (hb : d127768 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18162, d127768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18162, d127768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18163 q = 1) (hb : d127769 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18163, d127769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18163, d127769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d18171 q = 1) (hb : d127770 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18171, d127770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41531 q ha hb
    | true =>
      simp only [d18171, d127770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41539 q ha hb
  have h12 (q : Pattern) (ha : d18172 q = 1) (hb : d127771 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18172, d127771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18172, d127771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d18173 q = 1) (hb : d127772 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18173, d127772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18173, d127772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d18174 q = 1) (hb : d127773 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18174, d127773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18174, d127773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d18175 q = 1) (hb : d127774 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18175, d127774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18175, d127774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d18176 q = 1) (hb : d127775 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18176, d127775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d18176, d127775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro41541 (p : Pattern) (ha : d18181 p = 1) (hb : d127780 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18161 q = 1) (hb : d127767 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18161, d127767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41537 q ha hb
    | true =>
      simp only [d18161, d127767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41531 q ha hb
  have h2 (q : Pattern) (ha : d18162 q = 1) (hb : d127768 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18162, d127768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18162, d127768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18163 q = 1) (hb : d127769 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18163, d127769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18163, d127769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18171 q = 1) (hb : d127770 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18171, d127770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41531 q ha hb
    | true =>
      simp only [d18171, d127770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41539 q ha hb
  have h5 (q : Pattern) (ha : d18172 q = 1) (hb : d127771 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18172, d127771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18172, d127771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18173 q = 1) (hb : d127772 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18173, d127772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18173, d127772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d18174 q = 1) (hb : d127773 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18174, d127773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18174, d127773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18179 q = 1) (hb : d127778 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18179, d127778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18179, d127778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d18180 q = 1) (hb : d127779 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18180, d127779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18180, d127779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18181 q = 1) (hb : d127780 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18181, d127780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d18181, d127780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro41542 (p : Pattern) (ha : d18187 p = 1) (hb : d127786 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18177 q = 1) (hb : d127776 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18177, d127776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41540 q ha hb
    | true =>
      simp only [d18177, d127776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18178 q = 1) (hb : d127777 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18178, d127777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18178, d127777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18182 q = 1) (hb : d127781 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18182, d127781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41541 q ha hb
    | true =>
      simp only [d18182, d127781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18183 q = 1) (hb : d127782 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18183, d127782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18183, d127782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18184 q = 1) (hb : d127783 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18184, d127783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18184, d127783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18185 q = 1) (hb : d127784 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18185, d127784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18185, d127784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d18186 q = 1) (hb : d127785 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18186, d127785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18186, d127785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d18187 q = 1) (hb : d127786 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18187, d127786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18187, d127786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro41543 (p : Pattern) (ha : d18203 p = 1) (hb : d127798 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18182 q = 1) (hb : d127781 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18182, d127781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41541 q ha hb
    | true =>
      simp only [d18182, d127781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18183 q = 1) (hb : d127782 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18183, d127782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18183, d127782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18198 q = 1) (hb : d127793 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18198, d127793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41533 q ha hb
    | true =>
      simp only [d18198, d127793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18199 q = 1) (hb : d127794 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18199, d127794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18199, d127794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18200 q = 1) (hb : d127795 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18200, d127795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18200, d127795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18201 q = 1) (hb : d127796 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18201, d127796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18201, d127796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d18202 q = 1) (hb : d127797 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18202, d127797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18202, d127797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d18203 q = 1) (hb : d127798 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18203, d127798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18203, d127798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro41544 (p : Pattern) (ha : d18263 p = 1) (hb : d113738 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1868 q = 1) (hb : d53194 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1868, d53194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1868, d53194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro209 q ha hb
  have h2 (q : Pattern) (ha : d1582 q = 1) (hb : d53023 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1582, d53023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro209 q ha hb
    | true =>
      simp only [d1582, d53023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1869 q = 1) (hb : d53195 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1869, d53195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1869, d53195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53024 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d18188 q = 1) (hb : d53196 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18188, d53196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18188, d53196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18189 q = 1) (hb : d53197 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18189, d53197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18189, d53197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d18190 q = 1) (hb : d53203 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18190, d53203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18190, d53203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d18263 q = 1) (hb : d113738 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18263, d113738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18263, d113738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro41545 (p : Pattern) (ha : d18269 p = 1) (hb : d127819 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18161 q = 1) (hb : d127767 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18161, d127767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41537 q ha hb
    | true =>
      simp only [d18161, d127767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41531 q ha hb
  have h2 (q : Pattern) (ha : d18162 q = 1) (hb : d127768 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18162, d127768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18162, d127768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18163 q = 1) (hb : d127769 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18163, d127769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18163, d127769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18171 q = 1) (hb : d127770 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18171, d127770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41531 q ha hb
    | true =>
      simp only [d18171, d127770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41539 q ha hb
  have h5 (q : Pattern) (ha : d18172 q = 1) (hb : d127771 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18172, d127771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18172, d127771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18173 q = 1) (hb : d127772 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18173, d127772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18173, d127772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d18174 q = 1) (hb : d127773 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18174, d127773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18174, d127773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18264 q = 1) (hb : d127814 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18264, d127814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41531 q ha hb
    | true =>
      simp only [d18264, d127814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41544 q ha hb
  have h9 (q : Pattern) (ha : d18265 q = 1) (hb : d127815 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18265, d127815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18265, d127815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18266 q = 1) (hb : d127816 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18266, d127816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18266, d127816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d18267 q = 1) (hb : d127817 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18267, d127817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18267, d127817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d18268 q = 1) (hb : d127818 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18268, d127818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18268, d127818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d18269 q = 1) (hb : d127819 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18269, d127819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d18269, d127819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro41546 (p : Pattern) (ha : d18275 p = 1) (hb : d127825 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18270 q = 1) (hb : d127820 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18270, d127820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41545 q ha hb
    | true =>
      simp only [d18270, d127820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18271 q = 1) (hb : d127821 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18271, d127821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18271, d127821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18272 q = 1) (hb : d127822 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18272, d127822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18272, d127822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18273 q = 1) (hb : d127823 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18273, d127823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18273, d127823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18274 q = 1) (hb : d127824 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18274, d127824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18274, d127824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18275 q = 1) (hb : d127825 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18275, d127825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18275, d127825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41547 (p : Pattern) (ha : d127831 p = 1) (hb : d129389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18204 q = 1) (hb : d127799 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18204, d127799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41542 q ha hb
    | true =>
      simp only [d18204, d127799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41543 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d127812 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d127813 q = 1) (hb : d129385 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d127813, d129385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127813, d129385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d18276 q = 1) (hb : d127826 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18276, d127826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41546 q ha hb
    | true =>
      simp only [d18276, d127826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18277 q = 1) (hb : d127827 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d18277, d127827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18277, d127827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d127828 q = 1) (hb : d129386 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d127828, d129386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d127828, d129386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d127829 q = 1) (hb : d129387 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d127829, d129387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127829, d129387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d127830 q = 1) (hb : d129388 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d127830, d129388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127830, d129388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d127831 q = 1) (hb : d129389 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d127831, d129389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127831, d129389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro41548 (p : Pattern) (ha : d127844 p = 1) (hb : d129395 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d127737 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d127832 q = 1) (hb : d129390 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d127832, d129390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127832, d129390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41547 q ha hb
  have h3 (q : Pattern) (ha : d18293 q = 1) (hb : d127839 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d18293, d127839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18293, d127839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41535 q ha hb
  have h4 (q : Pattern) (ha : d127840 q = 1) (hb : d129391 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d127840, d129391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d127840, d129391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d127841 q = 1) (hb : d129392 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d127841, d129392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d127841, d129392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d127842 q = 1) (hb : d129393 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d127842, d129393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d127842, d129393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d127843 q = 1) (hb : d129394 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d127843, d129394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d127843, d129394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d127844 q = 1) (hb : d129395 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d127844, d129395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127844, d129395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41549 (p : Pattern) (ha : d127850 p = 1) (hb : d129401 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127845 q = 1) (hb : d129396 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d127845, d129396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127845, d129396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41548 q ha hb
  have h2 (q : Pattern) (ha : d127846 q = 1) (hb : d129397 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d127846, d129397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127846, d129397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127847 q = 1) (hb : d129398 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d127847, d129398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127847, d129398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d127848 q = 1) (hb : d129399 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d127848, d129399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127848, d129399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d127849 q = 1) (hb : d129400 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d127849, d129400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127849, d129400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d127850 q = 1) (hb : d129401 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d127850, d129401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127850, d129401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41550 (p : Pattern) (ha : d18341 p = 1) (hb : d128058 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2340 q = 1) (hb : d53505 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2340, d53505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2340, d53505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro267 q ha hb
  have h2 (q : Pattern) (ha : d2053 q = 1) (hb : d53332 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2053, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro267 q ha hb
    | true =>
      simp only [d2053, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2341 q = 1) (hb : d53506 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2341, d53506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2341, d53506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53333 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d18336 q = 1) (hb : d53507 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18336, d53507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18336, d53507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18337 q = 1) (hb : d53508 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18337, d53508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18337, d53508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17391 q = 1) (hb : d128053 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17391, d128053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17391, d128053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23359 q ha hb
  have h8 (q : Pattern) (ha : d10391 q = 1) (hb : d101712 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10391, d101712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23359 q ha hb
    | true =>
      simp only [d10391, d101712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17392 q = 1) (hb : d128054 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17392, d128054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17392, d128054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d101714 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d18338 q = 1) (hb : d128055 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18338, d128055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d18338, d128055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d18339 q = 1) (hb : d128056 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18339, d128056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d18339, d128056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d18340 q = 1) (hb : d128057 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18340, d128057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18340, d128057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d15775 q = 1) (hb : d123728 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15775, d123728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15775, d123728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23358 q ha hb
  have h15 (q : Pattern) (ha : d10371 q = 1) (hb : d101692 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10371, d101692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23358 q ha hb
    | true =>
      simp only [d10371, d101692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d15776 q = 1) (hb : d123729 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15776, d123729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d15776, d123729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d101694 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d18323 q = 1) (hb : d123730 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18323, d123730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d18323, d123730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d18324 q = 1) (hb : d123731 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18324, d123731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d18324, d123731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d18330 q = 1) (hb : d123732 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18330, d123732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d18330, d123732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d18341 q = 1) (hb : d128058 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18341, d128058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d18341, d128058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro41551 (p : Pattern) (ha : d18372 p = 1) (hb : d123766 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2346 q = 1) (hb : d53511 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2346, d53511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2346, d53511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro268 q ha hb
  have h2 (q : Pattern) (ha : d2065 q = 1) (hb : d53344 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2065, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro268 q ha hb
    | true =>
      simp only [d2065, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2347 q = 1) (hb : d53512 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2347, d53512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2347, d53512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53345 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d18369 q = 1) (hb : d53513 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18369, d53513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18369, d53513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18370 q = 1) (hb : d53514 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18370, d53514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18370, d53514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d18371 q = 1) (hb : d53520 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18371, d53520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18371, d53520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15790 q = 1) (hb : d123743 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15790, d123743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15790, d123743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23361 q ha hb
  have h9 (q : Pattern) (ha : d10412 q = 1) (hb : d101733 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10412, d101733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23361 q ha hb
    | true =>
      simp only [d10412, d101733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15791 q = 1) (hb : d123744 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15791, d123744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15791, d123744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d101735 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d18348 q = 1) (hb : d123745 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18348, d123745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18348, d123745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d18349 q = 1) (hb : d123746 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18349, d123746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d18349, d123746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d18350 q = 1) (hb : d123747 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18350, d123747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d18350, d123747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d18372 q = 1) (hb : d123766 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18372, d123766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18372, d123766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro41552 (p : Pattern) (ha : d18378 p = 1) (hb : d128084 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18373 q = 1) (hb : d128079 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18373, d128079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41550 q ha hb
    | true =>
      simp only [d18373, d128079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41551 q ha hb
  have h2 (q : Pattern) (ha : d18374 q = 1) (hb : d128080 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18374, d128080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18374, d128080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18375 q = 1) (hb : d128081 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18375, d128081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18375, d128081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18376 q = 1) (hb : d128082 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18376, d128082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18376, d128082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18377 q = 1) (hb : d128083 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18377, d128083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18377, d128083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18378 q = 1) (hb : d128084 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18378, d128084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18378, d128084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41553 (p : Pattern) (ha : d18467 p = 1) (hb : d128103 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18379 q = 1) (hb : d128085 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18379, d128085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41552 q ha hb
    | true =>
      simp only [d18379, d128085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18380 q = 1) (hb : d128086 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18380, d128086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18380, d128086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18464 q = 1) (hb : d128100 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18464, d128100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18464, d128100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18465 q = 1) (hb : d128101 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18465, d128101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18465, d128101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18466 q = 1) (hb : d128102 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18466, d128102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18466, d128102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18467 q = 1) (hb : d128103 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18467, d128103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18467, d128103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41554 (p : Pattern) (ha : d18473 p = 1) (hb : d128130 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18468 q = 1) (hb : d128125 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18468, d128125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41553 q ha hb
    | true =>
      simp only [d18468, d128125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18469 q = 1) (hb : d128126 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d18469, d128126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18469, d128126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18470 q = 1) (hb : d128127 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d18470, d128127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18470, d128127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18471 q = 1) (hb : d128128 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d18471, d128128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18471, d128128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18472 q = 1) (hb : d128129 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d18472, d128129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18472, d128129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18473 q = 1) (hb : d128130 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d18473, d128130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18473, d128130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41555 (p : Pattern) (ha : d18317 p = 1) (hb : d128037 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2331 q = 1) (hb : d53496 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2331, d53496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2331, d53496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro289 q ha hb
  have h2 (q : Pattern) (ha : d2144 q = 1) (hb : d53423 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2144, d53423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro289 q ha hb
    | true =>
      simp only [d2144, d53423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2332 q = 1) (hb : d53497 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2332, d53497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2332, d53497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53424 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d18309 q = 1) (hb : d53498 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18309, d53498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18309, d53498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18310 q = 1) (hb : d53499 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18310, d53499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18310, d53499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17369 q = 1) (hb : d128031 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17369, d128031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17369, d128031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23366 q ha hb
  have h8 (q : Pattern) (ha : d10343 q = 1) (hb : d101664 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10343, d101664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23366 q ha hb
    | true =>
      simp only [d10343, d101664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17370 q = 1) (hb : d128032 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17370, d128032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17370, d128032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d101666 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d18311 q = 1) (hb : d128033 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18311, d128033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d18311, d128033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d18312 q = 1) (hb : d128034 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18312, d128034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d18312, d128034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d18313 q = 1) (hb : d128035 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18313, d128035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18313, d128035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d13813 q = 1) (hb : d113965 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13813, d113965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13813, d113965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23367 q ha hb
  have h15 (q : Pattern) (ha : d10353 q = 1) (hb : d101674 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23367 q ha hb
    | true =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d13814 q = 1) (hb : d113966 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13814, d113966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d13814, d113966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d101676 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d18314 q = 1) (hb : d113967 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18314, d113967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d18314, d113967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d18315 q = 1) (hb : d113968 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18315, d113968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d18315, d113968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d18316 q = 1) (hb : d128036 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18316, d128036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18316, d128036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d18317 q = 1) (hb : d128037 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18317, d128037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d18317, d128037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro41556 (p : Pattern) (ha : d18326 p = 1) (hb : d128044 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2335 q = 1) (hb : d53500 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2335, d53500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2335, d53500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro262 q ha hb
  have h2 (q : Pattern) (ha : d2035 q = 1) (hb : d53314 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2035, d53314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro262 q ha hb
    | true =>
      simp only [d2035, d53314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2336 q = 1) (hb : d53501 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2336, d53501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2336, d53501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53315 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d18318 q = 1) (hb : d53502 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18318, d53502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18318, d53502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18319 q = 1) (hb : d53503 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18319, d53503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18319, d53503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17376 q = 1) (hb : d128038 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17376, d128038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17376, d128038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23369 q ha hb
  have h8 (q : Pattern) (ha : d10364 q = 1) (hb : d101685 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10364, d101685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23369 q ha hb
    | true =>
      simp only [d10364, d101685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17377 q = 1) (hb : d128039 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17377, d128039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17377, d128039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d101687 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d18320 q = 1) (hb : d128040 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18320, d128040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d18320, d128040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d18321 q = 1) (hb : d128041 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18321, d128041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d18321, d128041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d18322 q = 1) (hb : d128042 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18322, d128042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18322, d128042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d13813 q = 1) (hb : d113965 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13813, d113965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13813, d113965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23367 q ha hb
  have h15 (q : Pattern) (ha : d10353 q = 1) (hb : d101674 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23367 q ha hb
    | true =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d13814 q = 1) (hb : d113966 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13814, d113966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d13814, d113966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d101676 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d18314 q = 1) (hb : d113967 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18314, d113967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d18314, d113967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d18315 q = 1) (hb : d113968 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18315, d113968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d18315, d113968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d15775 q = 1) (hb : d123728 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15775, d123728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15775, d123728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23358 q ha hb
  have h21 (q : Pattern) (ha : d10371 q = 1) (hb : d101692 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10371, d101692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23358 q ha hb
    | true =>
      simp only [d10371, d101692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d15776 q = 1) (hb : d123729 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15776, d123729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d15776, d123729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d0 q = 1) (hb : d101694 q = 1) : d0 q = 1 := by
    exact ha
  have h24 (q : Pattern) (ha : d18323 q = 1) (hb : d123730 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18323, d123730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d18323, d123730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d18324 q = 1) (hb : d123731 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18324, d123731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d18324, d123731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d18325 q = 1) (hb : d128043 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18325, d128043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d18325, d128043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d18326 q = 1) (hb : d128044 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18326, d128044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d18326, d128044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro41557 (p : Pattern) (ha : d18331 p = 1) (hb : d128048 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13813 q = 1) (hb : d113965 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13813, d113965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13813, d113965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23367 q ha hb
  have h2 (q : Pattern) (ha : d10353 q = 1) (hb : d101674 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23367 q ha hb
    | true =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13814 q = 1) (hb : d113966 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13814, d113966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13814, d113966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d101676 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d18314 q = 1) (hb : d113967 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18314, d113967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18314, d113967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18315 q = 1) (hb : d113968 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18315, d113968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18315, d113968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15775 q = 1) (hb : d123728 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15775, d123728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15775, d123728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23358 q ha hb
  have h8 (q : Pattern) (ha : d10371 q = 1) (hb : d101692 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10371, d101692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23358 q ha hb
    | true =>
      simp only [d10371, d101692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d15776 q = 1) (hb : d123729 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15776, d123729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15776, d123729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d101694 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d18323 q = 1) (hb : d123730 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18323, d123730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d18323, d123730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d18324 q = 1) (hb : d123731 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18324, d123731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d18324, d123731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d18325 q = 1) (hb : d128043 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18325, d128043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18325, d128043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d18330 q = 1) (hb : d123732 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18330, d123732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d18330, d123732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d18331 q = 1) (hb : d128048 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18331, d128048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d18331, d128048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro41558 (p : Pattern) (ha : d18351 p = 1) (hb : d123748 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6643 q = 1) (hb : d76361 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d6643, d76361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6643, d76361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7980 q ha hb
  have h2 (q : Pattern) (ha : d5247 q = 1) (hb : d69331 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5247, d69331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7980 q ha hb
    | true =>
      simp only [d5247, d69331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6644 q = 1) (hb : d76362 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d6644, d76362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6644, d76362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d69332 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d18345 q = 1) (hb : d76363 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18345, d76363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18345, d76363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18346 q = 1) (hb : d76364 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18346, d76364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18346, d76364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d18347 q = 1) (hb : d76365 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18347, d76365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18347, d76365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15790 q = 1) (hb : d123743 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15790, d123743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15790, d123743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23361 q ha hb
  have h9 (q : Pattern) (ha : d10412 q = 1) (hb : d101733 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10412, d101733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23361 q ha hb
    | true =>
      simp only [d10412, d101733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15791 q = 1) (hb : d123744 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15791, d123744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15791, d123744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d101735 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d18348 q = 1) (hb : d123745 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18348, d123745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18348, d123745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d18349 q = 1) (hb : d123746 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18349, d123746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d18349, d123746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d18350 q = 1) (hb : d123747 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18350, d123747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d18350, d123747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d18351 q = 1) (hb : d123748 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18351, d123748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18351, d123748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro41559 (p : Pattern) (ha : d18357 p = 1) (hb : d128067 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18327 q = 1) (hb : d128045 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18327, d128045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41555 q ha hb
    | true =>
      simp only [d18327, d128045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41556 q ha hb
  have h2 (q : Pattern) (ha : d18328 q = 1) (hb : d128046 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18328, d128046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18328, d128046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18329 q = 1) (hb : d128047 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18329, d128047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18329, d128047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18332 q = 1) (hb : d128049 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18332, d128049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41556 q ha hb
    | true =>
      simp only [d18332, d128049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41557 q ha hb
  have h5 (q : Pattern) (ha : d18333 q = 1) (hb : d128050 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18333, d128050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18333, d128050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18334 q = 1) (hb : d128051 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18334, d128051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18334, d128051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d18335 q = 1) (hb : d128052 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18335, d128052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18335, d128052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18342 q = 1) (hb : d128059 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18342, d128059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41556 q ha hb
    | true =>
      simp only [d18342, d128059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41550 q ha hb
  have h9 (q : Pattern) (ha : d18343 q = 1) (hb : d128060 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18343, d128060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18343, d128060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18344 q = 1) (hb : d128061 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18344, d128061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18344, d128061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d18352 q = 1) (hb : d128062 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18352, d128062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41550 q ha hb
    | true =>
      simp only [d18352, d128062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41558 q ha hb
  have h12 (q : Pattern) (ha : d18353 q = 1) (hb : d128063 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18353, d128063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18353, d128063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d18354 q = 1) (hb : d128064 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18354, d128064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18354, d128064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d18355 q = 1) (hb : d128065 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18355, d128065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18355, d128065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d18356 q = 1) (hb : d128066 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18356, d128066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18356, d128066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d18357 q = 1) (hb : d128067 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18357, d128067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d18357, d128067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro41560 (p : Pattern) (ha : d18362 p = 1) (hb : d128072 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18342 q = 1) (hb : d128059 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18342, d128059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41556 q ha hb
    | true =>
      simp only [d18342, d128059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41550 q ha hb
  have h2 (q : Pattern) (ha : d18343 q = 1) (hb : d128060 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18343, d128060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18343, d128060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18344 q = 1) (hb : d128061 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18344, d128061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18344, d128061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18352 q = 1) (hb : d128062 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18352, d128062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41550 q ha hb
    | true =>
      simp only [d18352, d128062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41558 q ha hb
  have h5 (q : Pattern) (ha : d18353 q = 1) (hb : d128063 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18353, d128063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18353, d128063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18354 q = 1) (hb : d128064 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18354, d128064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18354, d128064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d18355 q = 1) (hb : d128065 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18355, d128065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18355, d128065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18360 q = 1) (hb : d128070 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18360, d128070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18360, d128070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d18361 q = 1) (hb : d128071 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18361, d128071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18361, d128071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18362 q = 1) (hb : d128072 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18362, d128072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d18362, d128072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro41561 (p : Pattern) (ha : d18368 p = 1) (hb : d128078 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18358 q = 1) (hb : d128068 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18358, d128068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41559 q ha hb
    | true =>
      simp only [d18358, d128068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18359 q = 1) (hb : d128069 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18359, d128069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18359, d128069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18363 q = 1) (hb : d128073 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18363, d128073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41560 q ha hb
    | true =>
      simp only [d18363, d128073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18364 q = 1) (hb : d128074 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18364, d128074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18364, d128074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18365 q = 1) (hb : d128075 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18365, d128075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18365, d128075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18366 q = 1) (hb : d128076 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18366, d128076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18366, d128076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d18367 q = 1) (hb : d128077 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18367, d128077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18367, d128077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d18368 q = 1) (hb : d128078 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18368, d128078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18368, d128078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro41562 (p : Pattern) (ha : d18384 p = 1) (hb : d128090 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18363 q = 1) (hb : d128073 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18363, d128073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41560 q ha hb
    | true =>
      simp only [d18363, d128073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18364 q = 1) (hb : d128074 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18364, d128074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18364, d128074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18379 q = 1) (hb : d128085 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18379, d128085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41552 q ha hb
    | true =>
      simp only [d18379, d128085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18380 q = 1) (hb : d128086 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18380, d128086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18380, d128086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18381 q = 1) (hb : d128087 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18381, d128087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18381, d128087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18382 q = 1) (hb : d128088 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18382, d128088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18382, d128088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d18383 q = 1) (hb : d128089 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18383, d128089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18383, d128089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d18384 q = 1) (hb : d128090 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18384, d128090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18384, d128090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro41563 (p : Pattern) (ha : d18444 p = 1) (hb : d113995 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2346 q = 1) (hb : d53511 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2346, d53511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2346, d53511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro268 q ha hb
  have h2 (q : Pattern) (ha : d2065 q = 1) (hb : d53344 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2065, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro268 q ha hb
    | true =>
      simp only [d2065, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2347 q = 1) (hb : d53512 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2347, d53512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2347, d53512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53345 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d18369 q = 1) (hb : d53513 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18369, d53513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18369, d53513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18370 q = 1) (hb : d53514 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18370, d53514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18370, d53514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d18371 q = 1) (hb : d53520 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18371, d53520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18371, d53520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d18444 q = 1) (hb : d113995 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18444, d113995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18444, d113995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro41564 (p : Pattern) (ha : d18450 p = 1) (hb : d128111 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18342 q = 1) (hb : d128059 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18342, d128059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41556 q ha hb
    | true =>
      simp only [d18342, d128059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41550 q ha hb
  have h2 (q : Pattern) (ha : d18343 q = 1) (hb : d128060 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18343, d128060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18343, d128060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18344 q = 1) (hb : d128061 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18344, d128061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18344, d128061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18352 q = 1) (hb : d128062 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18352, d128062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41550 q ha hb
    | true =>
      simp only [d18352, d128062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41558 q ha hb
  have h5 (q : Pattern) (ha : d18353 q = 1) (hb : d128063 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18353, d128063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18353, d128063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18354 q = 1) (hb : d128064 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18354, d128064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18354, d128064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d18355 q = 1) (hb : d128065 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18355, d128065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18355, d128065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18445 q = 1) (hb : d128106 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18445, d128106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41550 q ha hb
    | true =>
      simp only [d18445, d128106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41563 q ha hb
  have h9 (q : Pattern) (ha : d18446 q = 1) (hb : d128107 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18446, d128107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18446, d128107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18447 q = 1) (hb : d128108 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18447, d128108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18447, d128108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d18448 q = 1) (hb : d128109 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18448, d128109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18448, d128109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d18449 q = 1) (hb : d128110 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18449, d128110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18449, d128110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d18450 q = 1) (hb : d128111 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18450, d128111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d18450, d128111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro41565 (p : Pattern) (ha : d18456 p = 1) (hb : d128117 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18451 q = 1) (hb : d128112 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18451, d128112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41564 q ha hb
    | true =>
      simp only [d18451, d128112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18452 q = 1) (hb : d128113 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18452, d128113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18452, d128113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18453 q = 1) (hb : d128114 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18453, d128114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18453, d128114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18454 q = 1) (hb : d128115 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18454, d128115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18454, d128115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18455 q = 1) (hb : d128116 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18455, d128116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18455, d128116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18456 q = 1) (hb : d128117 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18456, d128117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18456, d128117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41566 (p : Pattern) (ha : d128123 p = 1) (hb : d129410 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18385 q = 1) (hb : d128091 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18385, d128091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41561 q ha hb
    | true =>
      simp only [d18385, d128091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41562 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d128104 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d128105 q = 1) (hb : d129406 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128105, d129406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128105, d129406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d18457 q = 1) (hb : d128118 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18457, d128118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41565 q ha hb
    | true =>
      simp only [d18457, d128118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18458 q = 1) (hb : d128119 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d18458, d128119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18458, d128119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d128120 q = 1) (hb : d129407 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128120, d129407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128120, d129407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d128121 q = 1) (hb : d129408 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128121, d129408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128121, d129408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128122 q = 1) (hb : d129409 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128122, d129409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128122, d129409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128123 q = 1) (hb : d129410 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128123, d129410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128123, d129410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro41567 (p : Pattern) (ha : d128136 p = 1) (hb : d129416 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128030 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d128124 q = 1) (hb : d129411 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128124, d129411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128124, d129411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41566 q ha hb
  have h3 (q : Pattern) (ha : d18474 q = 1) (hb : d128131 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d18474, d128131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18474, d128131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41554 q ha hb
  have h4 (q : Pattern) (ha : d128132 q = 1) (hb : d129412 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128132, d129412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128132, d129412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d128133 q = 1) (hb : d129413 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128133, d129413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128133, d129413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d128134 q = 1) (hb : d129414 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128134, d129414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128134, d129414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d128135 q = 1) (hb : d129415 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128135, d129415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128135, d129415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d128136 q = 1) (hb : d129416 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128136, d129416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128136, d129416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41568 (p : Pattern) (ha : d128142 p = 1) (hb : d129422 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128137 q = 1) (hb : d129417 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128137, d129417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128137, d129417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41567 q ha hb
  have h2 (q : Pattern) (ha : d128138 q = 1) (hb : d129418 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128138, d129418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128138, d129418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128139 q = 1) (hb : d129419 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128139, d129419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128139, d129419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128140 q = 1) (hb : d129420 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128140, d129420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128140, d129420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128141 q = 1) (hb : d129421 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128141, d129421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128141, d129421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128142 q = 1) (hb : d129422 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128142, d129422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128142, d129422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41569 (p : Pattern) (ha : d128148 p = 1) (hb : d129428 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d127103 q = 1) (hb : d129345 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d127103, d129345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41482 q ha hb
    | true =>
      simp only [d127103, d129345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41495 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d127274 q = 1) (hb : d129363 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d127274, d129363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127274, d129363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41511 q ha hb
  have h3 (q : Pattern) (ha : d127275 q = 1) (hb : d129364 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d127275, d129364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d127275, d129364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d127558 q = 1) (hb : d129382 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d127558, d129382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127558, d129382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41530 q ha hb
  have h5 (q : Pattern) (ha : d127559 q = 1) (hb : d129383 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d127559, d129383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127559, d129383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d127560 q = 1) (hb : d129384 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d127560, d129384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d127560, d129384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d127851 q = 1) (hb : d129402 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d127851, d129402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127851, d129402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41549 q ha hb
  have h8 (q : Pattern) (ha : d127852 q = 1) (hb : d129403 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d127852, d129403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127852, d129403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d127853 q = 1) (hb : d129404 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d127853, d129404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127853, d129404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d127854 q = 1) (hb : d129405 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d127854, d129405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d127854, d129405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d128143 q = 1) (hb : d129423 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d128143, d129423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128143, d129423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41568 q ha hb
  have h12 (q : Pattern) (ha : d128144 q = 1) (hb : d129424 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d128144, d129424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128144, d129424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128145 q = 1) (hb : d129425 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d128145, d129425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128145, d129425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128146 q = 1) (hb : d129426 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d128146, d129426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128146, d129426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128147 q = 1) (hb : d129427 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d128147, d129427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128147, d129427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d128148 q = 1) (hb : d129428 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d128148, d129428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d128148, d129428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro41570 (p : Pattern) (ha : d128154 p = 1) (hb : d129434 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128149 q = 1) (hb : d129429 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d128149, d129429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41569 q ha hb
    | true =>
      simp only [d128149, d129429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128150 q = 1) (hb : d129430 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d128150, d129430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128150, d129430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d128151 q = 1) (hb : d129431 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d128151, d129431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128151, d129431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128152 q = 1) (hb : d129432 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d128152, d129432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128152, d129432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128153 q = 1) (hb : d129433 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d128153, d129433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128153, d129433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128154 q = 1) (hb : d129434 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d128154, d129434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128154, d129434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41571 (p : Pattern) (ha : d128160 p = 1) (hb : d129440 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128155 q = 1) (hb : d129435 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d128155, d129435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41570 q ha hb
    | true =>
      simp only [d128155, d129435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128156 q = 1) (hb : d129436 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d128156, d129436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128156, d129436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d128157 q = 1) (hb : d129437 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d128157, d129437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128157, d129437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128158 q = 1) (hb : d129438 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d128158, d129438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128158, d129438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128159 q = 1) (hb : d129439 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d128159, d129439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128159, d129439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128160 q = 1) (hb : d129440 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d128160, d129440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128160, d129440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41572 (p : Pattern) (ha : d128166 p = 1) (hb : d129446 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128161 q = 1) (hb : d129441 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d128161, d129441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41571 q ha hb
    | true =>
      simp only [d128161, d129441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128162 q = 1) (hb : d129442 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d128162, d129442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128162, d129442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d128163 q = 1) (hb : d129443 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d128163, d129443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128163, d129443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128164 q = 1) (hb : d129444 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d128164, d129444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128164, d129444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128165 q = 1) (hb : d129445 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d128165, d129445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128165, d129445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128166 q = 1) (hb : d129446 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d128166, d129446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128166, d129446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41573 (p : Pattern) (ha : d128172 p = 1) (hb : d129452 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128167 q = 1) (hb : d129447 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d128167, d129447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41572 q ha hb
    | true =>
      simp only [d128167, d129447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128168 q = 1) (hb : d129448 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d128168, d129448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128168, d129448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d128169 q = 1) (hb : d129449 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d128169, d129449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128169, d129449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128170 q = 1) (hb : d129450 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d128170, d129450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128170, d129450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128171 q = 1) (hb : d129451 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d128171, d129451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128171, d129451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128172 q = 1) (hb : d129452 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d128172, d129452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128172, d129452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41574 (p : Pattern) (ha : d128178 p = 1) (hb : d129458 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128173 q = 1) (hb : d129453 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d128173, d129453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41573 q ha hb
    | true =>
      simp only [d128173, d129453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128174 q = 1) (hb : d129454 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d128174, d129454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128174, d129454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d128175 q = 1) (hb : d129455 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d128175, d129455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128175, d129455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128176 q = 1) (hb : d129456 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d128176, d129456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128176, d129456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128177 q = 1) (hb : d129457 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d128177, d129457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128177, d129457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128178 q = 1) (hb : d129458 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d128178, d129458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128178, d129458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41575 (p : Pattern) (ha : d128184 p = 1) (hb : d129464 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128179 q = 1) (hb : d129459 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d128179, d129459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41574 q ha hb
    | true =>
      simp only [d128179, d129459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128180 q = 1) (hb : d129460 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d128180, d129460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128180, d129460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d128181 q = 1) (hb : d129461 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d128181, d129461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128181, d129461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128182 q = 1) (hb : d129462 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d128182, d129462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128182, d129462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128183 q = 1) (hb : d129463 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d128183, d129463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128183, d129463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128184 q = 1) (hb : d129464 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d128184, d129464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128184, d129464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41576 (p : Pattern) (ha : d128190 p = 1) (hb : d129470 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128185 q = 1) (hb : d129465 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d128185, d129465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41575 q ha hb
    | true =>
      simp only [d128185, d129465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128186 q = 1) (hb : d129466 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d128186, d129466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128186, d129466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d128187 q = 1) (hb : d129467 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d128187, d129467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128187, d129467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128188 q = 1) (hb : d129468 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d128188, d129468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128188, d129468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128189 q = 1) (hb : d129469 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d128189, d129469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128189, d129469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128190 q = 1) (hb : d129470 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d128190, d129470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128190, d129470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41577 (p : Pattern) (ha : d128579 p = 1) (hb : d173701 p = 1) : d173701 p = 1 := by
  have h0 (q : Pattern) (ha : d128579 q = 1) (hb : d173701 q = 1) : d173701 q = 1 := by
    exact hb
  exact h0 p ha hb
theorem andIntro41578 (p : Pattern) (ha : d17696 p = 1) (hb : d52067 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52062 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17577 q = 1) (hb : d51936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17577, d51936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41467 q ha hb
    | true =>
      simp only [d17577, d51936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d17692 q = 1) (hb : d52063 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17692, d52063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17692, d52063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d51937 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d17693 q = 1) (hb : d52064 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17693, d52064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17693, d52064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17694 q = 1) (hb : d52065 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17694, d52065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17694, d52065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17695 q = 1) (hb : d52066 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17695, d52066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17695, d52066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17696 q = 1) (hb : d52067 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d17696, d52067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17696, d52067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41579 (p : Pattern) (ha : d52073 p = 1) (hb : d61083 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52043 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17697 q = 1) (hb : d52068 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d17697, d52068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17697, d52068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41578 q ha hb
  have h3 (q : Pattern) (ha : d52069 q = 1) (hb : d61079 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d52069, d61079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d52069, d61079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h4 (q : Pattern) (ha : d52070 q = 1) (hb : d61080 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52070, d61080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d52070, d61080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h5 (q : Pattern) (ha : d52071 q = 1) (hb : d61081 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52071, d61081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d52071, d61081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d52072 q = 1) (hb : d61082 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d52072, d61082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d52072, d61082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d52073 q = 1) (hb : d61083 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d52073, d61083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52073, d61083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro41580 (p : Pattern) (ha : d61093 p = 1) (hb : d126930 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d126925 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17609 q = 1) (hb : d52062 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17609, d52062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41472 q ha hb
    | true =>
      simp only [d17609, d52062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41467 q ha hb
  have h3 (q : Pattern) (ha : d61089 q = 1) (hb : d126926 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d61089, d126926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61089, d126926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d74105 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d61090 q = 1) (hb : d126927 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d61090, d126927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61090, d126927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61091 q = 1) (hb : d126928 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d61091, d126928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61091, d126928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d61092 q = 1) (hb : d126929 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d61092, d126929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61092, d126929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d61093 q = 1) (hb : d126930 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d61093, d126930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61093, d126930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41581 (p : Pattern) (ha : d61099 p = 1) (hb : d126936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d126911 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d61094 q = 1) (hb : d126931 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d61094, d126931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61094, d126931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41580 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52210 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d61095 q = 1) (hb : d126932 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d61095, d126932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61095, d126932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61096 q = 1) (hb : d126933 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61096, d126933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61096, d126933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d61097 q = 1) (hb : d126934 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61097, d126934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61097, d126934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d61098 q = 1) (hb : d126935 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61098, d126935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d61098, d126935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d61099 q = 1) (hb : d126936 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61099, d126936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61099, d126936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41582 (p : Pattern) (ha : d61105 p = 1) (hb : d126942 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51951 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52074 q = 1) (hb : d61084 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d52074, d61084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52074, d61084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41579 q ha hb
  have h3 (q : Pattern) (ha : d52075 q = 1) (hb : d61085 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d52075, d61085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52075, d61085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d52076 q = 1) (hb : d61086 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d52076, d61086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52076, d61086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d52077 q = 1) (hb : d61087 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d52077, d61087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52077, d61087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52078 q = 1) (hb : d61088 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d52078, d61088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52078, d61088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d61100 q = 1) (hb : d126937 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61100, d126937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61100, d126937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41581 q ha hb
  have h8 (q : Pattern) (ha : d61101 q = 1) (hb : d126938 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61101, d126938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61101, d126938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d61102 q = 1) (hb : d126939 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61102, d126939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61102, d126939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d61103 q = 1) (hb : d126940 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61103, d126940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61103, d126940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d61104 q = 1) (hb : d126941 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61104, d126941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61104, d126941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d61105 q = 1) (hb : d126942 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61105, d126942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d61105, d126942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro41583 (p : Pattern) (ha : d127090 p = 1) (hb : d173535 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d127078 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d127079 q = 1) (hb : d173530 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d127079, d173530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41491 q hb ha
    | true =>
      simp only [d127079, d173530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41484 q hb ha
  have h3 (q : Pattern) (ha : d127080 q = 1) (hb : d173531 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d127080, d173531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127080, d173531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d127086 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d127087 q = 1) (hb : d173532 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d127087, d173532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d127087, d173532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d127088 q = 1) (hb : d173533 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d127088, d173533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127088, d173533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d127089 q = 1) (hb : d173534 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d127089, d173534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127089, d173534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d127090 q = 1) (hb : d173535 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d127090, d173535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127090, d173535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41584 (p : Pattern) (ha : d127096 p = 1) (hb : d173541 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d127046 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d127091 q = 1) (hb : d173536 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d127091, d173536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127091, d173536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41583 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52414 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d127092 q = 1) (hb : d173537 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d127092, d173537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d127092, d173537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d127093 q = 1) (hb : d173538 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d127093, d173538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d127093, d173538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d127094 q = 1) (hb : d173539 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d127094, d173539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d127094, d173539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d127095 q = 1) (hb : d173540 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d127095, d173540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d127095, d173540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d127096 q = 1) (hb : d173541 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d127096, d173541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127096, d173541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41585 (p : Pattern) (ha : d127102 p = 1) (hb : d173547 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127097 q = 1) (hb : d173542 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d127097, d173542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127097, d173542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41584 q ha hb
  have h2 (q : Pattern) (ha : d127098 q = 1) (hb : d173543 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d127098, d173543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127098, d173543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127099 q = 1) (hb : d173544 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d127099, d173544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127099, d173544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d127100 q = 1) (hb : d173545 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d127100, d173545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127100, d173545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d127101 q = 1) (hb : d173546 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d127101, d173546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127101, d173546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d127102 q = 1) (hb : d173547 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d127102, d173547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127102, d173547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41586 (p : Pattern) (ha : d127261 p = 1) (hb : d173554 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d127249 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d127250 q = 1) (hb : d173549 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d127250, d173549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41507 q hb ha
    | true =>
      simp only [d127250, d173549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41499 q hb ha
  have h3 (q : Pattern) (ha : d127251 q = 1) (hb : d173550 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d127251, d173550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127251, d173550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d127257 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d127258 q = 1) (hb : d173551 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d127258, d173551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d127258, d173551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d127259 q = 1) (hb : d173552 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d127259, d173552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127259, d173552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d127260 q = 1) (hb : d173553 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d127260, d173553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127260, d173553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d127261 q = 1) (hb : d173554 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d127261, d173554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127261, d173554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41587 (p : Pattern) (ha : d127267 p = 1) (hb : d173560 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d127212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d127262 q = 1) (hb : d173555 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d127262, d173555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127262, d173555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41586 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52651 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d127263 q = 1) (hb : d173556 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d127263, d173556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d127263, d173556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d127264 q = 1) (hb : d173557 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d127264, d173557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d127264, d173557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d127265 q = 1) (hb : d173558 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d127265, d173558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d127265, d173558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d127266 q = 1) (hb : d173559 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d127266, d173559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d127266, d173559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d127267 q = 1) (hb : d173560 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d127267, d173560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127267, d173560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41588 (p : Pattern) (ha : d127273 p = 1) (hb : d173566 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127268 q = 1) (hb : d173561 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d127268, d173561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127268, d173561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41587 q ha hb
  have h2 (q : Pattern) (ha : d127269 q = 1) (hb : d173562 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d127269, d173562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127269, d173562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127270 q = 1) (hb : d173563 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d127270, d173563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127270, d173563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d127271 q = 1) (hb : d173564 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d127271, d173564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127271, d173564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d127272 q = 1) (hb : d173565 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d127272, d173565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127272, d173565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d127273 q = 1) (hb : d173566 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d127273, d173566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127273, d173566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41589 (p : Pattern) (ha : d127508 p = 1) (hb : d173570 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17980 q = 1) (hb : d127474 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17980, d127474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41518 q ha hb
    | true =>
      simp only [d17980, d127474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41512 q ha hb
  have h2 (q : Pattern) (ha : d17981 q = 1) (hb : d127475 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17981, d127475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17981, d127475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17982 q = 1) (hb : d127476 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17982, d127476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17982, d127476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17990 q = 1) (hb : d127477 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17990, d127477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41512 q ha hb
    | true =>
      simp only [d17990, d127477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41520 q ha hb
  have h5 (q : Pattern) (ha : d17991 q = 1) (hb : d127478 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17991, d127478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17991, d127478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17992 q = 1) (hb : d127479 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17992, d127479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17992, d127479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17993 q = 1) (hb : d127480 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17993, d127480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17993, d127480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18009 q = 1) (hb : d127494 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18009, d127494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41512 q ha hb
    | true =>
      simp only [d18009, d127494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41513 q ha hb
  have h9 (q : Pattern) (ha : d18010 q = 1) (hb : d127495 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18010, d127495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18010, d127495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18011 q = 1) (hb : d127496 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18011, d127496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18011, d127496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d18012 q = 1) (hb : d127497 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18012, d127497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18012, d127497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d127507 q = 1) (hb : d173569 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d127507, d173569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d127507, d173569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d127508 q = 1) (hb : d173570 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d127508, d173570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d127508, d173570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro41590 (p : Pattern) (ha : d127514 p = 1) (hb : d173576 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127509 q = 1) (hb : d173571 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d127509, d173571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41589 q ha hb
    | true =>
      simp only [d127509, d173571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d127510 q = 1) (hb : d173572 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d127510, d173572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127510, d173572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18015 q = 1) (hb : d127500 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18015, d127500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41514 q ha hb
    | true =>
      simp only [d18015, d127500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18016 q = 1) (hb : d127501 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18016, d127501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18016, d127501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d127511 q = 1) (hb : d173573 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d127511, d173573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d127511, d173573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d127512 q = 1) (hb : d173574 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d127512, d173574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d127512, d173574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d127513 q = 1) (hb : d173575 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d127513, d173575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d127513, d173575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d127514 q = 1) (hb : d173576 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d127514, d173576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d127514, d173576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro41591 (p : Pattern) (ha : d127538 p = 1) (hb : d173582 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d127506 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d127519 q = 1) (hb : d173577 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d127519, d173577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41590 q ha hb
    | true =>
      simp only [d127519, d173577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41515 q hb ha
  have h3 (q : Pattern) (ha : d127520 q = 1) (hb : d173578 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d127520, d173578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127520, d173578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d127534 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d127535 q = 1) (hb : d173579 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d127535, d173579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d127535, d173579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d127536 q = 1) (hb : d173580 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d127536, d173580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127536, d173580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d127537 q = 1) (hb : d173581 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d127537, d173581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127537, d173581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d127538 q = 1) (hb : d173582 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d127538, d173582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127538, d173582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41592 (p : Pattern) (ha : d127551 p = 1) (hb : d173588 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d127449 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d127539 q = 1) (hb : d173583 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d127539, d173583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127539, d173583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41591 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d127546 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d127547 q = 1) (hb : d173584 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d127547, d173584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d127547, d173584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d127548 q = 1) (hb : d173585 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d127548, d173585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d127548, d173585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d127549 q = 1) (hb : d173586 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d127549, d173586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d127549, d173586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d127550 q = 1) (hb : d173587 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d127550, d173587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d127550, d173587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d127551 q = 1) (hb : d173588 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d127551, d173588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127551, d173588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41593 (p : Pattern) (ha : d127557 p = 1) (hb : d173594 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127552 q = 1) (hb : d173589 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d127552, d173589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127552, d173589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41592 q ha hb
  have h2 (q : Pattern) (ha : d127553 q = 1) (hb : d173590 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d127553, d173590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127553, d173590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127554 q = 1) (hb : d173591 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d127554, d173591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127554, d173591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d127555 q = 1) (hb : d173592 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d127555, d173592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127555, d173592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d127556 q = 1) (hb : d173593 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d127556, d173593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127556, d173593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d127557 q = 1) (hb : d173594 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d127557, d173594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127557, d173594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41594 (p : Pattern) (ha : d127801 p = 1) (hb : d173599 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18161 q = 1) (hb : d127767 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18161, d127767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41537 q ha hb
    | true =>
      simp only [d18161, d127767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41531 q ha hb
  have h2 (q : Pattern) (ha : d18162 q = 1) (hb : d127768 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18162, d127768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18162, d127768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18163 q = 1) (hb : d127769 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18163, d127769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18163, d127769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18171 q = 1) (hb : d127770 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18171, d127770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41531 q ha hb
    | true =>
      simp only [d18171, d127770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41539 q ha hb
  have h5 (q : Pattern) (ha : d18172 q = 1) (hb : d127771 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18172, d127771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18172, d127771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18173 q = 1) (hb : d127772 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18173, d127772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18173, d127772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d18174 q = 1) (hb : d127773 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18174, d127773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18174, d127773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18192 q = 1) (hb : d127787 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18192, d127787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41531 q ha hb
    | true =>
      simp only [d18192, d127787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41532 q ha hb
  have h9 (q : Pattern) (ha : d18193 q = 1) (hb : d127788 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18193, d127788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18193, d127788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18194 q = 1) (hb : d127789 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18194, d127789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18194, d127789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d18195 q = 1) (hb : d127790 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18195, d127790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18195, d127790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d127800 q = 1) (hb : d173598 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d127800, d173598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d127800, d173598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d127801 q = 1) (hb : d173599 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d127801, d173599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d127801, d173599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro41595 (p : Pattern) (ha : d127807 p = 1) (hb : d173605 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127802 q = 1) (hb : d173600 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d127802, d173600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41594 q ha hb
    | true =>
      simp only [d127802, d173600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d127803 q = 1) (hb : d173601 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d127803, d173601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127803, d173601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18198 q = 1) (hb : d127793 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18198, d127793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41533 q ha hb
    | true =>
      simp only [d18198, d127793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18199 q = 1) (hb : d127794 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18199, d127794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18199, d127794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d127804 q = 1) (hb : d173602 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d127804, d173602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d127804, d173602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d127805 q = 1) (hb : d173603 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d127805, d173603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d127805, d173603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d127806 q = 1) (hb : d173604 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d127806, d173604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d127806, d173604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d127807 q = 1) (hb : d173605 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d127807, d173605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d127807, d173605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro41596 (p : Pattern) (ha : d127831 p = 1) (hb : d173611 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d127799 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d127812 q = 1) (hb : d173606 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d127812, d173606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41595 q ha hb
    | true =>
      simp only [d127812, d173606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41534 q hb ha
  have h3 (q : Pattern) (ha : d127813 q = 1) (hb : d173607 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d127813, d173607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127813, d173607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d127827 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d127828 q = 1) (hb : d173608 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d127828, d173608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d127828, d173608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d127829 q = 1) (hb : d173609 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d127829, d173609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127829, d173609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d127830 q = 1) (hb : d173610 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d127830, d173610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127830, d173610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d127831 q = 1) (hb : d173611 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d127831, d173611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127831, d173611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41597 (p : Pattern) (ha : d127844 p = 1) (hb : d173617 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d127737 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d127832 q = 1) (hb : d173612 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d127832, d173612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127832, d173612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41596 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d127839 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d127840 q = 1) (hb : d173613 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d127840, d173613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d127840, d173613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d127841 q = 1) (hb : d173614 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d127841, d173614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d127841, d173614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d127842 q = 1) (hb : d173615 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d127842, d173615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d127842, d173615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d127843 q = 1) (hb : d173616 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d127843, d173616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d127843, d173616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d127844 q = 1) (hb : d173617 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d127844, d173617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127844, d173617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41598 (p : Pattern) (ha : d127850 p = 1) (hb : d173623 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127845 q = 1) (hb : d173618 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d127845, d173618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127845, d173618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41597 q ha hb
  have h2 (q : Pattern) (ha : d127846 q = 1) (hb : d173619 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d127846, d173619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127846, d173619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127847 q = 1) (hb : d173620 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d127847, d173620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127847, d173620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d127848 q = 1) (hb : d173621 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d127848, d173621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127848, d173621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d127849 q = 1) (hb : d173622 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d127849, d173622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127849, d173622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d127850 q = 1) (hb : d173623 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d127850, d173623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127850, d173623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41599 (p : Pattern) (ha : d128093 p = 1) (hb : d173629 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18342 q = 1) (hb : d128059 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18342, d128059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41556 q ha hb
    | true =>
      simp only [d18342, d128059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41550 q ha hb
  have h2 (q : Pattern) (ha : d18343 q = 1) (hb : d128060 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18343, d128060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18343, d128060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18344 q = 1) (hb : d128061 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18344, d128061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18344, d128061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18352 q = 1) (hb : d128062 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18352, d128062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41550 q ha hb
    | true =>
      simp only [d18352, d128062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41558 q ha hb
  have h5 (q : Pattern) (ha : d18353 q = 1) (hb : d128063 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18353, d128063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18353, d128063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18354 q = 1) (hb : d128064 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18354, d128064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18354, d128064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d18355 q = 1) (hb : d128065 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18355, d128065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18355, d128065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18373 q = 1) (hb : d128079 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18373, d128079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41550 q ha hb
    | true =>
      simp only [d18373, d128079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41551 q ha hb
  have h9 (q : Pattern) (ha : d18374 q = 1) (hb : d128080 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18374, d128080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18374, d128080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18375 q = 1) (hb : d128081 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18375, d128081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18375, d128081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d18376 q = 1) (hb : d128082 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18376, d128082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18376, d128082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d128092 q = 1) (hb : d173628 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d128092, d173628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d128092, d173628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d128093 q = 1) (hb : d173629 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d128093, d173629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d128093, d173629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro41600 (p : Pattern) (ha : d128099 p = 1) (hb : d173635 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128094 q = 1) (hb : d173630 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d128094, d173630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41599 q ha hb
    | true =>
      simp only [d128094, d173630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128095 q = 1) (hb : d173631 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d128095, d173631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128095, d173631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18379 q = 1) (hb : d128085 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18379, d128085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41552 q ha hb
    | true =>
      simp only [d18379, d128085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18380 q = 1) (hb : d128086 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18380, d128086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18380, d128086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128096 q = 1) (hb : d173632 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d128096, d173632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128096, d173632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d128097 q = 1) (hb : d173633 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d128097, d173633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128097, d173633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d128098 q = 1) (hb : d173634 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d128098, d173634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128098, d173634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d128099 q = 1) (hb : d173635 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d128099, d173635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128099, d173635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro41601 (p : Pattern) (ha : d128123 p = 1) (hb : d173641 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128091 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d128104 q = 1) (hb : d173636 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d128104, d173636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41600 q ha hb
    | true =>
      simp only [d128104, d173636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41553 q hb ha
  have h3 (q : Pattern) (ha : d128105 q = 1) (hb : d173637 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128105, d173637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128105, d173637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d128119 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d128120 q = 1) (hb : d173638 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128120, d173638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128120, d173638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d128121 q = 1) (hb : d173639 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128121, d173639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128121, d173639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128122 q = 1) (hb : d173640 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128122, d173640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128122, d173640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128123 q = 1) (hb : d173641 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128123, d173641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128123, d173641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41602 (p : Pattern) (ha : d128136 p = 1) (hb : d173647 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128030 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d128124 q = 1) (hb : d173642 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128124, d173642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128124, d173642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41601 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d128131 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d128132 q = 1) (hb : d173643 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128132, d173643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128132, d173643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d128133 q = 1) (hb : d173644 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128133, d173644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128133, d173644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d128134 q = 1) (hb : d173645 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128134, d173645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128134, d173645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d128135 q = 1) (hb : d173646 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128135, d173646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128135, d173646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d128136 q = 1) (hb : d173647 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128136, d173647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128136, d173647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41603 (p : Pattern) (ha : d128142 p = 1) (hb : d173653 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128137 q = 1) (hb : d173648 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128137, d173648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128137, d173648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41602 q ha hb
  have h2 (q : Pattern) (ha : d128138 q = 1) (hb : d173649 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128138, d173649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128138, d173649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128139 q = 1) (hb : d173650 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128139, d173650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128139, d173650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128140 q = 1) (hb : d173651 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128140, d173651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128140, d173651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128141 q = 1) (hb : d173652 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128141, d173652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128141, d173652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128142 q = 1) (hb : d173653 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128142, d173653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128142, d173653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41604 (p : Pattern) (ha : d128148 p = 1) (hb : d173659 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d127103 q = 1) (hb : d173548 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d127103, d173548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41582 q hb ha
    | true =>
      simp only [d127103, d173548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41585 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d127274 q = 1) (hb : d173567 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d127274, d173567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127274, d173567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41588 q ha hb
  have h3 (q : Pattern) (ha : d127275 q = 1) (hb : d173568 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d127275, d173568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d127275, d173568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d127558 q = 1) (hb : d173595 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d127558, d173595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127558, d173595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41593 q ha hb
  have h5 (q : Pattern) (ha : d127559 q = 1) (hb : d173596 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d127559, d173596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127559, d173596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d127560 q = 1) (hb : d173597 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d127560, d173597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d127560, d173597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d127851 q = 1) (hb : d173624 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d127851, d173624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127851, d173624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41598 q ha hb
  have h8 (q : Pattern) (ha : d127852 q = 1) (hb : d173625 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d127852, d173625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127852, d173625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d127853 q = 1) (hb : d173626 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d127853, d173626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127853, d173626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d127854 q = 1) (hb : d173627 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d127854, d173627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d127854, d173627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d128143 q = 1) (hb : d173654 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d128143, d173654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128143, d173654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41603 q ha hb
  have h12 (q : Pattern) (ha : d128144 q = 1) (hb : d173655 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d128144, d173655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128144, d173655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128145 q = 1) (hb : d173656 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d128145, d173656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128145, d173656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128146 q = 1) (hb : d173657 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d128146, d173657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128146, d173657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128147 q = 1) (hb : d173658 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d128147, d173658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128147, d173658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d128148 q = 1) (hb : d173659 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d128148, d173659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d128148, d173659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro41605 (p : Pattern) (ha : d128154 p = 1) (hb : d173665 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128149 q = 1) (hb : d173660 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d128149, d173660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41604 q ha hb
    | true =>
      simp only [d128149, d173660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128150 q = 1) (hb : d173661 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d128150, d173661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128150, d173661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d128151 q = 1) (hb : d173662 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d128151, d173662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128151, d173662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128152 q = 1) (hb : d173663 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d128152, d173663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128152, d173663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128153 q = 1) (hb : d173664 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d128153, d173664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128153, d173664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128154 q = 1) (hb : d173665 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d128154, d173665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128154, d173665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41606 (p : Pattern) (ha : d128160 p = 1) (hb : d173671 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128155 q = 1) (hb : d173666 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d128155, d173666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41605 q ha hb
    | true =>
      simp only [d128155, d173666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128156 q = 1) (hb : d173667 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d128156, d173667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128156, d173667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d128157 q = 1) (hb : d173668 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d128157, d173668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128157, d173668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128158 q = 1) (hb : d173669 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d128158, d173669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128158, d173669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128159 q = 1) (hb : d173670 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d128159, d173670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128159, d173670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128160 q = 1) (hb : d173671 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d128160, d173671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128160, d173671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41607 (p : Pattern) (ha : d128166 p = 1) (hb : d173677 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128161 q = 1) (hb : d173672 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d128161, d173672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41606 q ha hb
    | true =>
      simp only [d128161, d173672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128162 q = 1) (hb : d173673 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d128162, d173673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128162, d173673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d128163 q = 1) (hb : d173674 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d128163, d173674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128163, d173674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128164 q = 1) (hb : d173675 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d128164, d173675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128164, d173675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128165 q = 1) (hb : d173676 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d128165, d173676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128165, d173676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128166 q = 1) (hb : d173677 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d128166, d173677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128166, d173677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41608 (p : Pattern) (ha : d128172 p = 1) (hb : d173683 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128167 q = 1) (hb : d173678 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d128167, d173678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41607 q ha hb
    | true =>
      simp only [d128167, d173678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128168 q = 1) (hb : d173679 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d128168, d173679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128168, d173679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d128169 q = 1) (hb : d173680 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d128169, d173680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128169, d173680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128170 q = 1) (hb : d173681 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d128170, d173681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128170, d173681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128171 q = 1) (hb : d173682 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d128171, d173682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128171, d173682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128172 q = 1) (hb : d173683 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d128172, d173683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128172, d173683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41609 (p : Pattern) (ha : d128178 p = 1) (hb : d173689 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128173 q = 1) (hb : d173684 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d128173, d173684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41608 q ha hb
    | true =>
      simp only [d128173, d173684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128174 q = 1) (hb : d173685 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d128174, d173685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128174, d173685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d128175 q = 1) (hb : d173686 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d128175, d173686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128175, d173686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128176 q = 1) (hb : d173687 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d128176, d173687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128176, d173687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128177 q = 1) (hb : d173688 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d128177, d173688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128177, d173688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128178 q = 1) (hb : d173689 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d128178, d173689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128178, d173689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41610 (p : Pattern) (ha : d128184 p = 1) (hb : d173695 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128179 q = 1) (hb : d173690 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d128179, d173690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41609 q ha hb
    | true =>
      simp only [d128179, d173690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128180 q = 1) (hb : d173691 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d128180, d173691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128180, d173691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d128181 q = 1) (hb : d173692 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d128181, d173692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128181, d173692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128182 q = 1) (hb : d173693 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d128182, d173693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128182, d173693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128183 q = 1) (hb : d173694 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d128183, d173694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128183, d173694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128184 q = 1) (hb : d173695 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d128184, d173695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128184, d173695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41611 (p : Pattern) (ha : d128190 p = 1) (hb : d173701 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128185 q = 1) (hb : d173696 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d128185, d173696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41610 q ha hb
    | true =>
      simp only [d128185, d173696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128186 q = 1) (hb : d173697 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d128186, d173697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128186, d173697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d128187 q = 1) (hb : d173698 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d128187, d173698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128187, d173698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128188 q = 1) (hb : d173699 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d128188, d173699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128188, d173699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128189 q = 1) (hb : d173700 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d128189, d173700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128189, d173700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128190 q = 1) (hb : d173701 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d128190, d173701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128190, d173701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41612 (p : Pattern) (ha : d4359 p = 1) (hb : d17696 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d244 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d17577 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4355 q = 1) (hb : d17692 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4355, d17692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d4355, d17692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d85 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4356 q = 1) (hb : d17693 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4356, d17693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4356, d17693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d4357 q = 1) (hb : d17694 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4357, d17694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4357, d17694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4358 q = 1) (hb : d17695 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4358, d17695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4358, d17695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4359 q = 1) (hb : d17696 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4359, d17696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4359, d17696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41613 (p : Pattern) (ha : d51652 p = 1) (hb : d61083 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51651 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4360 q = 1) (hb : d17697 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4360, d17697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4360, d17697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41612 q ha hb
  have h3 (q : Pattern) (ha : d4361 q = 1) (hb : d61079 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4361, d61079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4361, d61079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d4362 q = 1) (hb : d61080 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4362, d61080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4362, d61080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d4363 q = 1) (hb : d61081 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4363, d61081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4363, d61081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d4364 q = 1) (hb : d61082 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4364, d61082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4364, d61082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d51652 q = 1) (hb : d61083 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d51652, d61083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51652, d61083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro41614 (p : Pattern) (ha : d61093 p = 1) (hb : d128217 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16017 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d17609 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d61089 q = 1) (hb : d128213 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d61089, d128213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61089, d128213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d5379 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d61090 q = 1) (hb : d128214 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d61090, d128214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61090, d128214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61091 q = 1) (hb : d128215 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d61091, d128215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61091, d128215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d61092 q = 1) (hb : d128216 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d61092, d128216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61092, d128216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d61093 q = 1) (hb : d128217 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d61093, d128217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61093, d128217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41615 (p : Pattern) (ha : d61099 p = 1) (hb : d128223 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d61094 q = 1) (hb : d128218 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d61094, d128218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61094, d128218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41614 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d463 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d61095 q = 1) (hb : d128219 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d61095, d128219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61095, d128219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61096 q = 1) (hb : d128220 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61096, d128220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61096, d128220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d61097 q = 1) (hb : d128221 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61097, d128221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61097, d128221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d61098 q = 1) (hb : d128222 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61098, d128222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d61098, d128222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d61099 q = 1) (hb : d128223 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61099, d128223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61099, d128223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41616 (p : Pattern) (ha : d61105 p = 1) (hb : d128229 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d99 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51653 q = 1) (hb : d61084 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d51653, d61084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51653, d61084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41613 q ha hb
  have h3 (q : Pattern) (ha : d51654 q = 1) (hb : d61085 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d51654, d61085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51654, d61085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d51655 q = 1) (hb : d61086 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d51655, d61086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51655, d61086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51656 q = 1) (hb : d61087 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d51656, d61087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51656, d61087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51657 q = 1) (hb : d61088 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d51657, d61088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51657, d61088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d61100 q = 1) (hb : d128224 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61100, d128224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61100, d128224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41615 q ha hb
  have h8 (q : Pattern) (ha : d61101 q = 1) (hb : d128225 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61101, d128225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61101, d128225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d61102 q = 1) (hb : d128226 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61102, d128226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61102, d128226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d61103 q = 1) (hb : d128227 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61103, d128227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61103, d128227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d61104 q = 1) (hb : d128228 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61104, d128228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61104, d128228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d61105 q = 1) (hb : d128229 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61105, d128229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d61105, d128229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro41617 (p : Pattern) (ha : d128256 p = 1) (hb : d173535 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16187 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d173530 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d128252 q = 1) (hb : d173531 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128252, d173531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128252, d173531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d16209 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d128253 q = 1) (hb : d173532 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128253, d173532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128253, d173532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d128254 q = 1) (hb : d173533 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128254, d173533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128254, d173533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128255 q = 1) (hb : d173534 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128255, d173534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128255, d173534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128256 q = 1) (hb : d173535 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128256, d173535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128256, d173535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41618 (p : Pattern) (ha : d128262 p = 1) (hb : d173541 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128251 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d128257 q = 1) (hb : d173536 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128257, d173536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128257, d173536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41617 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d737 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d128258 q = 1) (hb : d173537 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128258, d173537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128258, d173537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d128259 q = 1) (hb : d173538 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128259, d173538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128259, d173538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d128260 q = 1) (hb : d173539 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128260, d173539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128260, d173539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d128261 q = 1) (hb : d173540 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128261, d173540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128261, d173540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d128262 q = 1) (hb : d173541 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128262, d173541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128262, d173541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41619 (p : Pattern) (ha : d128268 p = 1) (hb : d173547 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128263 q = 1) (hb : d173542 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128263, d173542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128263, d173542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41618 q ha hb
  have h2 (q : Pattern) (ha : d128264 q = 1) (hb : d173543 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128264, d173543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128264, d173543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128265 q = 1) (hb : d173544 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128265, d173544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128265, d173544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128266 q = 1) (hb : d173545 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128266, d173545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128266, d173545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128267 q = 1) (hb : d173546 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128267, d173546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128267, d173546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128268 q = 1) (hb : d173547 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128268, d173547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128268, d173547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41620 (p : Pattern) (ha : d128296 p = 1) (hb : d173554 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16392 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d173549 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d128292 q = 1) (hb : d173550 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128292, d173550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128292, d173550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d16419 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d128293 q = 1) (hb : d173551 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128293, d173551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128293, d173551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d128294 q = 1) (hb : d173552 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128294, d173552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128294, d173552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128295 q = 1) (hb : d173553 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128295, d173553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128295, d173553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128296 q = 1) (hb : d173554 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128296, d173554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128296, d173554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41621 (p : Pattern) (ha : d128302 p = 1) (hb : d173560 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128291 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d128297 q = 1) (hb : d173555 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128297, d173555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128297, d173555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41620 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1070 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d128298 q = 1) (hb : d173556 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128298, d173556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128298, d173556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d128299 q = 1) (hb : d173557 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128299, d173557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128299, d173557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d128300 q = 1) (hb : d173558 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128300, d173558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128300, d173558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d128301 q = 1) (hb : d173559 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128301, d173559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128301, d173559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d128302 q = 1) (hb : d173560 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128302, d173560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128302, d173560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41622 (p : Pattern) (ha : d128308 p = 1) (hb : d173566 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128303 q = 1) (hb : d173561 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128303, d173561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128303, d173561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41621 q ha hb
  have h2 (q : Pattern) (ha : d128304 q = 1) (hb : d173562 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128304, d173562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128304, d173562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128305 q = 1) (hb : d173563 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128305, d173563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128305, d173563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128306 q = 1) (hb : d173564 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128306, d173564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128306, d173564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128307 q = 1) (hb : d173565 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128307, d173565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128307, d173565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128308 q = 1) (hb : d173566 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128308, d173566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128308, d173566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41623 (p : Pattern) (ha : d128337 p = 1) (hb : d173582 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16705 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d173577 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d128333 q = 1) (hb : d173578 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128333, d173578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128333, d173578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d16756 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d128334 q = 1) (hb : d173579 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128334, d173579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128334, d173579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d128335 q = 1) (hb : d173580 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128335, d173580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128335, d173580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128336 q = 1) (hb : d173581 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128336, d173581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128336, d173581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128337 q = 1) (hb : d173582 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128337, d173582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128337, d173582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41624 (p : Pattern) (ha : d128343 p = 1) (hb : d173588 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128332 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d128338 q = 1) (hb : d173583 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128338, d173583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128338, d173583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41623 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d16772 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d128339 q = 1) (hb : d173584 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128339, d173584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128339, d173584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d128340 q = 1) (hb : d173585 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128340, d173585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128340, d173585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d128341 q = 1) (hb : d173586 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128341, d173586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128341, d173586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d128342 q = 1) (hb : d173587 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128342, d173587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128342, d173587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d128343 q = 1) (hb : d173588 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128343, d173588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128343, d173588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41625 (p : Pattern) (ha : d128349 p = 1) (hb : d173594 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128344 q = 1) (hb : d173589 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128344, d173589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128344, d173589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41624 q ha hb
  have h2 (q : Pattern) (ha : d128345 q = 1) (hb : d173590 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128345, d173590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128345, d173590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128346 q = 1) (hb : d173591 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128346, d173591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128346, d173591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128347 q = 1) (hb : d173592 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128347, d173592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128347, d173592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128348 q = 1) (hb : d173593 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128348, d173593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128348, d173593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128349 q = 1) (hb : d173594 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128349, d173594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128349, d173594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41626 (p : Pattern) (ha : d128379 p = 1) (hb : d173611 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d17065 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d173606 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d128375 q = 1) (hb : d173607 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128375, d173607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128375, d173607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d17121 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d128376 q = 1) (hb : d173608 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128376, d173608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128376, d173608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d128377 q = 1) (hb : d173609 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128377, d173609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128377, d173609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128378 q = 1) (hb : d173610 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128378, d173610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128378, d173610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128379 q = 1) (hb : d173611 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128379, d173611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128379, d173611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41627 (p : Pattern) (ha : d128385 p = 1) (hb : d173617 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d128380 q = 1) (hb : d173612 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128380, d173612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128380, d173612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41626 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d17137 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d128381 q = 1) (hb : d173613 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128381, d173613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128381, d173613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d128382 q = 1) (hb : d173614 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128382, d173614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128382, d173614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d128383 q = 1) (hb : d173615 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128383, d173615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128383, d173615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d128384 q = 1) (hb : d173616 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128384, d173616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128384, d173616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d128385 q = 1) (hb : d173617 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128385, d173617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128385, d173617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41628 (p : Pattern) (ha : d128391 p = 1) (hb : d173623 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128386 q = 1) (hb : d173618 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128386, d173618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128386, d173618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41627 q ha hb
  have h2 (q : Pattern) (ha : d128387 q = 1) (hb : d173619 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128387, d173619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128387, d173619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128388 q = 1) (hb : d173620 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128388, d173620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128388, d173620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128389 q = 1) (hb : d173621 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128389, d173621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128389, d173621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128390 q = 1) (hb : d173622 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128390, d173622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128390, d173622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128391 q = 1) (hb : d173623 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128391, d173623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128391, d173623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41629 (p : Pattern) (ha : d128422 p = 1) (hb : d173641 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d17429 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d173636 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d128418 q = 1) (hb : d173637 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128418, d173637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128418, d173637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d17485 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d128419 q = 1) (hb : d173638 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128419, d173638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128419, d173638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d128420 q = 1) (hb : d173639 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128420, d173639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128420, d173639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128421 q = 1) (hb : d173640 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128421, d173640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128421, d173640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128422 q = 1) (hb : d173641 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128422, d173641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128422, d173641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41630 (p : Pattern) (ha : d128428 p = 1) (hb : d173647 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128417 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d128423 q = 1) (hb : d173642 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128423, d173642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128423, d173642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41629 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d17501 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d128424 q = 1) (hb : d173643 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128424, d173643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128424, d173643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d128425 q = 1) (hb : d173644 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128425, d173644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128425, d173644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d128426 q = 1) (hb : d173645 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128426, d173645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128426, d173645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d128427 q = 1) (hb : d173646 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128427, d173646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128427, d173646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d128428 q = 1) (hb : d173647 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128428, d173647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128428, d173647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41631 (p : Pattern) (ha : d128434 p = 1) (hb : d173653 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128429 q = 1) (hb : d173648 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128429, d173648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128429, d173648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41630 q ha hb
  have h2 (q : Pattern) (ha : d128430 q = 1) (hb : d173649 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128430, d173649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128430, d173649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128431 q = 1) (hb : d173650 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128431, d173650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128431, d173650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128432 q = 1) (hb : d173651 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128432, d173651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128432, d173651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128433 q = 1) (hb : d173652 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128433, d173652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128433, d173652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128434 q = 1) (hb : d173653 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128434, d173653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128434, d173653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41632 (p : Pattern) (ha : d128440 p = 1) (hb : d173659 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d128269 q = 1) (hb : d173548 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d128269, d173548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41616 q hb ha
    | true =>
      simp only [d128269, d173548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41619 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d128309 q = 1) (hb : d173567 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d128309, d173567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128309, d173567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41622 q ha hb
  have h3 (q : Pattern) (ha : d128310 q = 1) (hb : d173568 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d128310, d173568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128310, d173568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128350 q = 1) (hb : d173595 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d128350, d173595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128350, d173595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41625 q ha hb
  have h5 (q : Pattern) (ha : d128351 q = 1) (hb : d173596 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d128351, d173596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128351, d173596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128352 q = 1) (hb : d173597 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d128352, d173597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128352, d173597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128392 q = 1) (hb : d173624 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d128392, d173624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128392, d173624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41628 q ha hb
  have h8 (q : Pattern) (ha : d128393 q = 1) (hb : d173625 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d128393, d173625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128393, d173625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128394 q = 1) (hb : d173626 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d128394, d173626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128394, d173626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d128395 q = 1) (hb : d173627 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d128395, d173627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128395, d173627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d128435 q = 1) (hb : d173654 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d128435, d173654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128435, d173654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41631 q ha hb
  have h12 (q : Pattern) (ha : d128436 q = 1) (hb : d173655 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d128436, d173655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128436, d173655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128437 q = 1) (hb : d173656 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d128437, d173656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128437, d173656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128438 q = 1) (hb : d173657 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d128438, d173657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128438, d173657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128439 q = 1) (hb : d173658 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d128439, d173658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128439, d173658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d128440 q = 1) (hb : d173659 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d128440, d173659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d128440, d173659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro41633 (p : Pattern) (ha : d128446 p = 1) (hb : d173665 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128441 q = 1) (hb : d173660 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d128441, d173660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41632 q ha hb
    | true =>
      simp only [d128441, d173660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d128442 q = 1) (hb : d173661 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d128442, d173661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128442, d173661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d128443 q = 1) (hb : d173662 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d128443, d173662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128443, d173662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d128444 q = 1) (hb : d173663 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d128444, d173663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128444, d173663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128445 q = 1) (hb : d173664 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d128445, d173664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128445, d173664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d128446 q = 1) (hb : d173665 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d128446, d173665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128446, d173665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41634 (p : Pattern) (ha : d128452 p = 1) (hb : d173671 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128447 q = 1) (hb : d173666 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d128447, d173666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41633 q ha hb
    | true =>
      simp only [d128447, d173666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d128448 q = 1) (hb : d173667 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d128448, d173667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128448, d173667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d128449 q = 1) (hb : d173668 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d128449, d173668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128449, d173668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d128450 q = 1) (hb : d173669 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d128450, d173669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128450, d173669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128451 q = 1) (hb : d173670 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d128451, d173670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128451, d173670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d128452 q = 1) (hb : d173671 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d128452, d173671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128452, d173671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41635 (p : Pattern) (ha : d128458 p = 1) (hb : d173677 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128453 q = 1) (hb : d173672 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d128453, d173672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41634 q ha hb
    | true =>
      simp only [d128453, d173672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d128454 q = 1) (hb : d173673 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d128454, d173673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128454, d173673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d128455 q = 1) (hb : d173674 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d128455, d173674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128455, d173674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d128456 q = 1) (hb : d173675 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d128456, d173675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128456, d173675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128457 q = 1) (hb : d173676 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d128457, d173676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128457, d173676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d128458 q = 1) (hb : d173677 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d128458, d173677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128458, d173677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41636 (p : Pattern) (ha : d128464 p = 1) (hb : d173683 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128459 q = 1) (hb : d173678 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d128459, d173678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41635 q ha hb
    | true =>
      simp only [d128459, d173678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d128460 q = 1) (hb : d173679 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d128460, d173679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128460, d173679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d128461 q = 1) (hb : d173680 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d128461, d173680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128461, d173680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d128462 q = 1) (hb : d173681 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d128462, d173681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128462, d173681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128463 q = 1) (hb : d173682 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d128463, d173682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128463, d173682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d128464 q = 1) (hb : d173683 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d128464, d173683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128464, d173683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41637 (p : Pattern) (ha : d128470 p = 1) (hb : d173689 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128465 q = 1) (hb : d173684 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d128465, d173684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41636 q ha hb
    | true =>
      simp only [d128465, d173684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d128466 q = 1) (hb : d173685 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d128466, d173685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128466, d173685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d128467 q = 1) (hb : d173686 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d128467, d173686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128467, d173686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d128468 q = 1) (hb : d173687 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d128468, d173687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128468, d173687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128469 q = 1) (hb : d173688 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d128469, d173688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128469, d173688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d128470 q = 1) (hb : d173689 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d128470, d173689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128470, d173689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41638 (p : Pattern) (ha : d128476 p = 1) (hb : d173695 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128471 q = 1) (hb : d173690 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d128471, d173690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41637 q ha hb
    | true =>
      simp only [d128471, d173690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d128472 q = 1) (hb : d173691 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d128472, d173691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128472, d173691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d128473 q = 1) (hb : d173692 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d128473, d173692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128473, d173692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d128474 q = 1) (hb : d173693 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d128474, d173693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128474, d173693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128475 q = 1) (hb : d173694 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d128475, d173694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128475, d173694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d128476 q = 1) (hb : d173695 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d128476, d173695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128476, d173695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41639 (p : Pattern) (ha : d128482 p = 1) (hb : d173701 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128477 q = 1) (hb : d173696 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d128477, d173696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41638 q ha hb
    | true =>
      simp only [d128477, d173696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d128478 q = 1) (hb : d173697 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d128478, d173697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128478, d173697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d128479 q = 1) (hb : d173698 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d128479, d173698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128479, d173698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d128480 q = 1) (hb : d173699 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d128480, d173699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128480, d173699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128481 q = 1) (hb : d173700 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d128481, d173700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128481, d173700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d128482 q = 1) (hb : d173701 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d128482, d173701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128482, d173701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41640 (p : Pattern) (ha : d17564 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d17561 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17562 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17562, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d17562, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17563 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17563, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17563, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d17564 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41641 (p : Pattern) (ha : d17570 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17565 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41640 q ha hb
    | true =>
      simp only [d17565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17566 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17567 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17568 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17569 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17570 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41642 (p : Pattern) (ha : d17576 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17571 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41641 q ha hb
    | true =>
      simp only [d17571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17572 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17573 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17574 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17575 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17576 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41643 (p : Pattern) (ha : d17582 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17577 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41642 q ha hb
    | true =>
      simp only [d17577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17578 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d17579 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17580 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17581 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17582 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d17582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41644 (p : Pattern) (ha : d17588 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17583 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d17583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41643 q ha hb
  have h2 (q : Pattern) (ha : d17584 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d17584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d17585 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d17585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17586 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d17586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17587 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d17587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17588 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d17588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41645 (p : Pattern) (ha : d17596 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d17593 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17594 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17594, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d17594, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d17562 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17595 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17595, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17595, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d17561 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d17562 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17562, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d17562, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d17563 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17563, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17563, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d17596 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro41646 (p : Pattern) (ha : d17602 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17597 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41645 q ha hb
    | true =>
      simp only [d17597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41640 q ha hb
  have h2 (q : Pattern) (ha : d17598 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17599 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17565 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41640 q ha hb
    | true =>
      simp only [d17565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17566 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17567 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17600 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17568 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17601 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17602 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro41647 (p : Pattern) (ha : d17608 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17603 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41646 q ha hb
    | true =>
      simp only [d17603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17604 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17571 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41641 q ha hb
    | true =>
      simp only [d17571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17572 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17605 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17606 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17607 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17608 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro41648 (p : Pattern) (ha : d60563 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17609 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41647 q ha hb
    | true =>
      simp only [d17609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41642 q ha hb
  have h2 (q : Pattern) (ha : d60559 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d60559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d60559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d17577 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41642 q ha hb
    | true =>
      simp only [d17577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17578 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d60560 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d60560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d60560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d60561 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d60561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d60561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d60562 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d60562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d60562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d60563 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d60563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d60563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41649 (p : Pattern) (ha : d60569 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d60564 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d60564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d60564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41648 q ha hb
  have h2 (q : Pattern) (ha : d60565 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d60565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d60565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d60566 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d60566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d60566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d60567 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d60567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d60567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d60568 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d60568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d60568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d60569 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d60569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d60569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41650 (p : Pattern) (ha : d17696 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17577 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41642 q ha hb
    | true =>
      simp only [d17577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17692 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17693 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17694 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17695 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17696 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d17696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41651 (p : Pattern) (ha : d17649 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d17643 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17644 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17644, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d17644, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d17594 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17645 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17645, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17645, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d17646 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d17647 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17647, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d17647, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d17562 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d17648 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17648, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17648, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d17649 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro41652 (p : Pattern) (ha : d17655 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17650 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41651 q ha hb
    | true =>
      simp only [d17650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41645 q ha hb
  have h2 (q : Pattern) (ha : d17651 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17652 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17597 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41645 q ha hb
    | true =>
      simp only [d17597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41640 q ha hb
  have h5 (q : Pattern) (ha : d17598 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17599 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17653 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17565 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41640 q ha hb
    | true =>
      simp only [d17565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17566 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17567 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17600 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d17654 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d17655 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d17655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro41653 (p : Pattern) (ha : d17661 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17656 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41652 q ha hb
    | true =>
      simp only [d17656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17657 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17603 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41646 q ha hb
    | true =>
      simp only [d17603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17604 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17658 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17659 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17660 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17661 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro41654 (p : Pattern) (ha : d17684 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17603 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41646 q ha hb
    | true =>
      simp only [d17603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17604 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17681 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17682 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17683 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17684 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41655 (p : Pattern) (ha : d129315 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17662 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41653 q ha hb
    | true =>
      simp only [d17662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41647 q ha hb
  have h2 (q : Pattern) (ha : d129311 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d17685 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41654 q ha hb
    | true =>
      simp only [d17685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17686 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129312 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129313 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129314 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129315 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41656 (p : Pattern) (ha : d129321 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129316 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41655 q ha hb
  have h2 (q : Pattern) (ha : d17697 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d17697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41650 q ha hb
  have h3 (q : Pattern) (ha : d129317 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129318 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129319 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129320 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d129321 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro41657 (p : Pattern) (ha : d129327 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17589 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d17589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41644 q ha hb
  have h2 (q : Pattern) (ha : d17590 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d17590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17591 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d17591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17592 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d17592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d60570 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d60570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d60570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41649 q ha hb
  have h6 (q : Pattern) (ha : d60571 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d60571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d60571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d60572 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d60572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d60572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d60573 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d60573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d60573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d60574 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d60574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d60574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d129322 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41656 q ha hb
  have h11 (q : Pattern) (ha : d129323 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d129324 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d129325 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d129326 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d129327 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d129327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro41658 (p : Pattern) (ha : d17740 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17597 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41645 q ha hb
    | true =>
      simp only [d17597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41640 q ha hb
  have h2 (q : Pattern) (ha : d17598 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17599 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17730 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17739 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17740 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41659 (p : Pattern) (ha : d17792 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17741 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41658 q ha hb
    | true =>
      simp only [d17741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17742 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17789 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17790 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17791 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17792 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41660 (p : Pattern) (ha : d17798 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17793 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41659 q ha hb
    | true =>
      simp only [d17793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17794 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17795 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17796 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17797 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17798 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d17798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41661 (p : Pattern) (ha : d17717 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d17709 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17710 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17710, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d17710, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d17712 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17713 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17713, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17713, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d17714 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d17715 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17715, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d17715, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d17647 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d17716 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17716, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17716, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d17717 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro41662 (p : Pattern) (ha : d17721 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d17646 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17647 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17647, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d17647, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d17562 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17648 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17648, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17648, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d17561 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d17562 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17562, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d17562, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d17563 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17563, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17563, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d17721 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro41663 (p : Pattern) (ha : d17727 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17718 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41661 q ha hb
    | true =>
      simp only [d17718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41651 q ha hb
  have h2 (q : Pattern) (ha : d17719 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17720 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17722 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41651 q ha hb
    | true =>
      simp only [d17722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41662 q ha hb
  have h5 (q : Pattern) (ha : d17723 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17724 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17725 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17650 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41651 q ha hb
    | true =>
      simp only [d17650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41645 q ha hb
  have h9 (q : Pattern) (ha : d17651 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17652 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17597 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41645 q ha hb
    | true =>
      simp only [d17597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41640 q ha hb
  have h12 (q : Pattern) (ha : d17598 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d17599 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d17653 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d17726 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d17727 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d17727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro41664 (p : Pattern) (ha : d17732 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17650 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41651 q ha hb
    | true =>
      simp only [d17650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41645 q ha hb
  have h2 (q : Pattern) (ha : d17651 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17652 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17597 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41645 q ha hb
    | true =>
      simp only [d17597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41640 q ha hb
  have h5 (q : Pattern) (ha : d17598 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17599 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17653 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17730 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17731 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17732 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro41665 (p : Pattern) (ha : d17738 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17728 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41663 q ha hb
    | true =>
      simp only [d17728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17729 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17733 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41664 q ha hb
    | true =>
      simp only [d17733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17734 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17735 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17736 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17737 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17738 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro41666 (p : Pattern) (ha : d17746 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17733 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41664 q ha hb
    | true =>
      simp only [d17733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17734 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17741 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41658 q ha hb
    | true =>
      simp only [d17741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17742 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17743 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17744 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17745 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17746 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro41667 (p : Pattern) (ha : d17781 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17733 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41664 q ha hb
    | true =>
      simp only [d17733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17734 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17778 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17779 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17780 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17781 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41668 (p : Pattern) (ha : d129332 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17747 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41665 q ha hb
    | true =>
      simp only [d17747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41666 q ha hb
  have h2 (q : Pattern) (ha : d129328 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d17782 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41667 q ha hb
    | true =>
      simp only [d17782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17783 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129329 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129330 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129331 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129332 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41669 (p : Pattern) (ha : d129338 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129333 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41668 q ha hb
  have h2 (q : Pattern) (ha : d17799 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d17799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41660 q ha hb
  have h3 (q : Pattern) (ha : d129334 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129335 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129336 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129337 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d129338 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro41670 (p : Pattern) (ha : d129344 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129339 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41669 q ha hb
  have h2 (q : Pattern) (ha : d129340 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129341 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129342 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129343 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129344 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41671 (p : Pattern) (ha : d17835 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d17643 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17644 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17644, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d17644, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d17822 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17834 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17834, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17834, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d17821 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d17822 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17822, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d17822, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d17828 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17828, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17828, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d17835 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro41672 (p : Pattern) (ha : d17839 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d17821 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17822 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17822, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d17822, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17828 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17828, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17828, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d17839 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41673 (p : Pattern) (ha : d17858 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17840 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41671 q ha hb
    | true =>
      simp only [d17840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41672 q ha hb
  have h2 (q : Pattern) (ha : d17841 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17842 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17848 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17857 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17858 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41674 (p : Pattern) (ha : d17921 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17859 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41673 q ha hb
    | true =>
      simp only [d17859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17860 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17918 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17919 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17920 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17921 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41675 (p : Pattern) (ha : d17927 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17922 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41674 q ha hb
    | true =>
      simp only [d17922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17923 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17924 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17925 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17926 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17927 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d17927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41676 (p : Pattern) (ha : d17820 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d17812 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17813 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17813, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d17813, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d17815 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17816 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17816, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17816, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d17817 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d17818 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17818, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d17818, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d17715 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d17819 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17819, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17819, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d17820 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro41677 (p : Pattern) (ha : d17824 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d17709 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17710 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17710, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d17710, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d17712 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17713 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17713, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17713, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d17714 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d17715 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17715, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d17715, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d17822 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d17823 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17823, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17823, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d17824 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro41678 (p : Pattern) (ha : d17829 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d17714 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17715 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17715, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d17715, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d17822 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17823 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17823, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17823, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d17821 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d17822 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17822, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d17822, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d17828 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17828, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17828, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d17829 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro41679 (p : Pattern) (ha : d17845 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17825 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41676 q ha hb
    | true =>
      simp only [d17825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41677 q ha hb
  have h2 (q : Pattern) (ha : d17826 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17827 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17830 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41677 q ha hb
    | true =>
      simp only [d17830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41678 q ha hb
  have h5 (q : Pattern) (ha : d17831 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17832 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17833 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17836 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41677 q ha hb
    | true =>
      simp only [d17836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41671 q ha hb
  have h9 (q : Pattern) (ha : d17837 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17838 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17840 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41671 q ha hb
    | true =>
      simp only [d17840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41672 q ha hb
  have h12 (q : Pattern) (ha : d17841 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d17842 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d17843 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d17844 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d17845 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d17845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro41680 (p : Pattern) (ha : d17850 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17836 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41677 q ha hb
    | true =>
      simp only [d17836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41671 q ha hb
  have h2 (q : Pattern) (ha : d17837 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17838 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17840 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41671 q ha hb
    | true =>
      simp only [d17840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41672 q ha hb
  have h5 (q : Pattern) (ha : d17841 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17842 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17843 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17848 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17849 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17850 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro41681 (p : Pattern) (ha : d17856 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17846 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41679 q ha hb
    | true =>
      simp only [d17846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17847 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17851 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41680 q ha hb
    | true =>
      simp only [d17851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17852 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17853 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17854 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17855 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17856 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro41682 (p : Pattern) (ha : d17864 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17851 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41680 q ha hb
    | true =>
      simp only [d17851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17852 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17859 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41673 q ha hb
    | true =>
      simp only [d17859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17860 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17861 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17862 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17863 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17864 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro41683 (p : Pattern) (ha : d17910 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17851 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41680 q ha hb
    | true =>
      simp only [d17851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17852 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17907 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17908 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17909 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17910 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41684 (p : Pattern) (ha : d129350 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17865 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41681 q ha hb
    | true =>
      simp only [d17865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41682 q ha hb
  have h2 (q : Pattern) (ha : d129346 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d17911 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41683 q ha hb
    | true =>
      simp only [d17911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17912 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129347 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129348 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129349 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129350 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41685 (p : Pattern) (ha : d129356 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129351 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41684 q ha hb
  have h2 (q : Pattern) (ha : d17928 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d17928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41675 q ha hb
  have h3 (q : Pattern) (ha : d129352 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129353 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129354 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129355 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d129356 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro41686 (p : Pattern) (ha : d129362 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129357 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41685 q ha hb
  have h2 (q : Pattern) (ha : d129358 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129359 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129360 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129361 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129362 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41687 (p : Pattern) (ha : d17979 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d17974 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17975 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17975, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d17975, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d17977 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17978 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17978, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17978, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d17958 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d17959 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17959, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d17959, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d17968 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17968, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17968, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d17979 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro41688 (p : Pattern) (ha : d18008 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d17976 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17977 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17977, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d17977, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18007 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18007, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18007, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d17986 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d17987 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17987, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d17987, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d17988 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17988, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17988, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d18008 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41689 (p : Pattern) (ha : d18014 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18009 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41687 q ha hb
    | true =>
      simp only [d18009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41688 q ha hb
  have h2 (q : Pattern) (ha : d18010 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18011 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18012 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18013 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18014 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41690 (p : Pattern) (ha : d18101 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18015 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41689 q ha hb
    | true =>
      simp only [d18015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18016 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18098 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18099 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18100 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18101 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41691 (p : Pattern) (ha : d18107 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18102 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41690 q ha hb
    | true =>
      simp only [d18102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18103 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d18103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18104 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d18104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18105 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d18105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18106 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d18106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18107 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d18107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41692 (p : Pattern) (ha : d17952 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d17942 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17943 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17943, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d17943, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d17945 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17946 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17946, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17946, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d17947 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d17948 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17948, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d17948, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d17950 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d17951 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17951, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17951, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d17952 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro41693 (p : Pattern) (ha : d17961 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d17953 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17954 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17954, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d17954, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d17956 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17957 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17957, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17957, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d17949 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d17950 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17950, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d17950, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d17959 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d17960 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17960, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17960, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d17961 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro41694 (p : Pattern) (ha : d17969 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d17965 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17966 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17966, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d17966, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d17959 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17967 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17967, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17967, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d17958 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d17959 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17959, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d17959, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d17968 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17968, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17968, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d17969 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro41695 (p : Pattern) (ha : d17989 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d17983 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17984 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17984, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d17984, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17985 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17985, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17985, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d17986 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d17987 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17987, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d17987, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d17988 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17988, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17988, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d17989 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41696 (p : Pattern) (ha : d17995 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17962 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41692 q ha hb
    | true =>
      simp only [d17962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41693 q ha hb
  have h2 (q : Pattern) (ha : d17963 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17964 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17970 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41693 q ha hb
    | true =>
      simp only [d17970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41694 q ha hb
  have h5 (q : Pattern) (ha : d17971 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17972 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17973 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17980 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41693 q ha hb
    | true =>
      simp only [d17980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41687 q ha hb
  have h9 (q : Pattern) (ha : d17981 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17982 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17990 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41687 q ha hb
    | true =>
      simp only [d17990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41695 q ha hb
  have h12 (q : Pattern) (ha : d17991 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d17992 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d17993 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d17994 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d17995 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d17995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro41697 (p : Pattern) (ha : d18000 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17980 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41693 q ha hb
    | true =>
      simp only [d17980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41687 q ha hb
  have h2 (q : Pattern) (ha : d17981 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17982 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17990 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41687 q ha hb
    | true =>
      simp only [d17990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41695 q ha hb
  have h5 (q : Pattern) (ha : d17991 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17992 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17993 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17998 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17999 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18000 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d18000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro41698 (p : Pattern) (ha : d18006 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17996 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41696 q ha hb
    | true =>
      simp only [d17996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17997 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18001 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41697 q ha hb
    | true =>
      simp only [d18001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18002 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18003 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18004 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d18005 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d18006 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro41699 (p : Pattern) (ha : d18020 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18001 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41697 q ha hb
    | true =>
      simp only [d18001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18002 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18015 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41689 q ha hb
    | true =>
      simp only [d18015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18016 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18017 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18018 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d18019 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d18020 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro41700 (p : Pattern) (ha : d18078 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d17976 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17977 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17977, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d17977, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18007 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18007, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18007, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d18078 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41701 (p : Pattern) (ha : d18084 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17980 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41693 q ha hb
    | true =>
      simp only [d17980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41687 q ha hb
  have h2 (q : Pattern) (ha : d17981 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17982 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17990 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41687 q ha hb
    | true =>
      simp only [d17990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41695 q ha hb
  have h5 (q : Pattern) (ha : d17991 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17992 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17993 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18079 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41687 q ha hb
    | true =>
      simp only [d18079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41700 q ha hb
  have h9 (q : Pattern) (ha : d18080 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18081 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d18082 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d18083 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d18084 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d18084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro41702 (p : Pattern) (ha : d18090 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18085 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41701 q ha hb
    | true =>
      simp only [d18085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18086 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18087 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18088 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18089 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18090 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41703 (p : Pattern) (ha : d129369 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18021 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41698 q ha hb
    | true =>
      simp only [d18021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41699 q ha hb
  have h2 (q : Pattern) (ha : d129365 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d18091 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41702 q ha hb
    | true =>
      simp only [d18091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18092 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d18092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129366 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129367 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129368 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129369 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41704 (p : Pattern) (ha : d129375 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129370 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41703 q ha hb
  have h2 (q : Pattern) (ha : d18108 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d18108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41691 q ha hb
  have h3 (q : Pattern) (ha : d129371 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129372 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129373 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129374 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d129375 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro41705 (p : Pattern) (ha : d129381 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129376 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41704 q ha hb
  have h2 (q : Pattern) (ha : d129377 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129378 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129379 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129380 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129381 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41706 (p : Pattern) (ha : d18160 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d18155 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d18156 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18156, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d18156, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d18158 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18159 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18159, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18159, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d18139 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d18140 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18140, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d18140, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d18149 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18149, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18149, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d18160 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro41707 (p : Pattern) (ha : d18191 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d18188 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d18189 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18189, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d18189, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18190 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18190, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18190, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d18167 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d18168 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18168, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d18168, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d18169 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18169, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18169, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d18191 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41708 (p : Pattern) (ha : d18197 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18192 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41706 q ha hb
    | true =>
      simp only [d18192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41707 q ha hb
  have h2 (q : Pattern) (ha : d18193 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18194 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18195 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18196 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18197 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41709 (p : Pattern) (ha : d18286 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18198 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41708 q ha hb
    | true =>
      simp only [d18198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18199 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18283 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18284 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18285 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18286 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41710 (p : Pattern) (ha : d18292 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18287 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41709 q ha hb
    | true =>
      simp only [d18287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18288 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d18288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18289 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d18289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18290 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d18290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18291 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d18291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18292 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d18292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41711 (p : Pattern) (ha : d18133 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d18123 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d18124 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18124, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d18124, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d18126 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18127 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18127, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18127, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d18128 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d18129 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18129, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d18129, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d18131 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d18132 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18132, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18132, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d18133 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro41712 (p : Pattern) (ha : d18142 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d18134 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d18135 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18135, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d18135, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d18137 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18138 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18138, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18138, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d18130 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d18131 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18131, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d18131, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d18140 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d18141 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18141, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18141, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d18142 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro41713 (p : Pattern) (ha : d18150 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d18146 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d18147 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18147, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d18147, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d18140 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18148 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18148, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18148, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d18139 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d18140 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18140, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d18140, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d18149 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18149, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18149, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d18150 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro41714 (p : Pattern) (ha : d18170 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d18164 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d18165 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18165, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d18165, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18166 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18166, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18166, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d18167 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d18168 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18168, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d18168, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d18169 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18169, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18169, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d18170 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41715 (p : Pattern) (ha : d18176 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18143 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41711 q ha hb
    | true =>
      simp only [d18143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41712 q ha hb
  have h2 (q : Pattern) (ha : d18144 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18145 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18151 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41712 q ha hb
    | true =>
      simp only [d18151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41713 q ha hb
  have h5 (q : Pattern) (ha : d18152 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18153 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d18154 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18161 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41712 q ha hb
    | true =>
      simp only [d18161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41706 q ha hb
  have h9 (q : Pattern) (ha : d18162 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18163 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d18171 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41706 q ha hb
    | true =>
      simp only [d18171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41714 q ha hb
  have h12 (q : Pattern) (ha : d18172 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d18173 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d18174 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d18175 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d18176 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d18176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro41716 (p : Pattern) (ha : d18181 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18161 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41712 q ha hb
    | true =>
      simp only [d18161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41706 q ha hb
  have h2 (q : Pattern) (ha : d18162 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18163 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18171 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41706 q ha hb
    | true =>
      simp only [d18171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41714 q ha hb
  have h5 (q : Pattern) (ha : d18172 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18173 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d18174 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18179 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d18180 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18181 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d18181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro41717 (p : Pattern) (ha : d18187 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18177 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41715 q ha hb
    | true =>
      simp only [d18177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18178 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18182 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41716 q ha hb
    | true =>
      simp only [d18182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18183 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18184 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18185 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d18186 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d18187 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro41718 (p : Pattern) (ha : d18203 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18182 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41716 q ha hb
    | true =>
      simp only [d18182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18183 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18198 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41708 q ha hb
    | true =>
      simp only [d18198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18199 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18200 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18201 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d18202 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d18203 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro41719 (p : Pattern) (ha : d18263 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d18188 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d18189 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18189, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d18189, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18190 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18190, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18190, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d18263 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41720 (p : Pattern) (ha : d18269 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18161 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41712 q ha hb
    | true =>
      simp only [d18161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41706 q ha hb
  have h2 (q : Pattern) (ha : d18162 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18163 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18171 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41706 q ha hb
    | true =>
      simp only [d18171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41714 q ha hb
  have h5 (q : Pattern) (ha : d18172 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18173 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d18174 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18264 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41706 q ha hb
    | true =>
      simp only [d18264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41719 q ha hb
  have h9 (q : Pattern) (ha : d18265 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18266 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d18267 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d18268 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d18269 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d18269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro41721 (p : Pattern) (ha : d18275 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18270 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41720 q ha hb
    | true =>
      simp only [d18270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18271 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18272 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18273 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18274 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18275 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41722 (p : Pattern) (ha : d129389 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18204 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41717 q ha hb
    | true =>
      simp only [d18204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41718 q ha hb
  have h2 (q : Pattern) (ha : d129385 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d18276 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41721 q ha hb
    | true =>
      simp only [d18276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18277 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d18277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129386 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129387 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129388 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129389 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41723 (p : Pattern) (ha : d129395 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129390 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41722 q ha hb
  have h2 (q : Pattern) (ha : d18293 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d18293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41710 q ha hb
  have h3 (q : Pattern) (ha : d129391 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129392 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129393 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129394 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d129395 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro41724 (p : Pattern) (ha : d129401 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129396 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41723 q ha hb
  have h2 (q : Pattern) (ha : d129397 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129398 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129399 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129400 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129401 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41725 (p : Pattern) (ha : d18341 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d18336 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d18337 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18337, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d18337, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d18339 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18340 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18340, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18340, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d18323 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d18324 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18324, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d18324, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d18330 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18330, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18330, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d18341 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro41726 (p : Pattern) (ha : d18372 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d18369 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d18370 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18370, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d18370, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18371 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18371, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18371, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d18348 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d18349 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18349, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d18349, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d18350 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18350, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18350, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d18372 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41727 (p : Pattern) (ha : d18378 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18373 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41725 q ha hb
    | true =>
      simp only [d18373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41726 q ha hb
  have h2 (q : Pattern) (ha : d18374 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18375 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18376 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18377 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18378 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41728 (p : Pattern) (ha : d18467 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18379 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41727 q ha hb
    | true =>
      simp only [d18379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18380 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18464 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18465 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18466 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18467 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41729 (p : Pattern) (ha : d18473 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18468 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41728 q ha hb
    | true =>
      simp only [d18468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18469 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d18469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18470 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d18470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18471 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d18471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18472 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d18472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18473 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d18473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41730 (p : Pattern) (ha : d18317 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d18309 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d18310 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18310, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d18310, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d18312 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18313 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18313, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18313, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d18315 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d18316 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18316, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18316, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d18317 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41731 (p : Pattern) (ha : d18326 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d18318 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d18319 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18319, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d18319, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d18321 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18322 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18322, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18322, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d18314 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d18315 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18315, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d18315, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d18324 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d18325 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18325, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18325, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d18326 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro41732 (p : Pattern) (ha : d18331 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d18314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d18315 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18315, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d18315, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d18324 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18325 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18325, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18325, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d18323 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d18324 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18324, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d18324, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d18330 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18330, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18330, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d18331 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro41733 (p : Pattern) (ha : d18351 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d18345 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d18346 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18346, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d18346, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18347 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18347, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18347, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d18348 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d18349 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18349, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d18349, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d18350 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18350, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18350, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d18351 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41734 (p : Pattern) (ha : d18357 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18327 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41730 q ha hb
    | true =>
      simp only [d18327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41731 q ha hb
  have h2 (q : Pattern) (ha : d18328 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18329 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18332 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41731 q ha hb
    | true =>
      simp only [d18332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41732 q ha hb
  have h5 (q : Pattern) (ha : d18333 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18334 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d18335 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18342 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41731 q ha hb
    | true =>
      simp only [d18342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41725 q ha hb
  have h9 (q : Pattern) (ha : d18343 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18344 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d18352 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41725 q ha hb
    | true =>
      simp only [d18352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41733 q ha hb
  have h12 (q : Pattern) (ha : d18353 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d18354 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d18355 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d18356 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d18357 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d18357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro41735 (p : Pattern) (ha : d18362 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18342 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41731 q ha hb
    | true =>
      simp only [d18342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41725 q ha hb
  have h2 (q : Pattern) (ha : d18343 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18344 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18352 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41725 q ha hb
    | true =>
      simp only [d18352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41733 q ha hb
  have h5 (q : Pattern) (ha : d18353 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18354 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d18355 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18360 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d18361 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18362 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d18362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro41736 (p : Pattern) (ha : d18368 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18358 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41734 q ha hb
    | true =>
      simp only [d18358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18359 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18363 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41735 q ha hb
    | true =>
      simp only [d18363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18364 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18365 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18366 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d18367 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d18368 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro41737 (p : Pattern) (ha : d18384 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18363 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41735 q ha hb
    | true =>
      simp only [d18363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18364 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18379 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41727 q ha hb
    | true =>
      simp only [d18379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18380 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18381 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18382 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d18383 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d18384 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro41738 (p : Pattern) (ha : d18444 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d18369 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d18370 q = 1) (hb : d163683 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18370, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d18370, d163683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18371 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18371, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18371, d163684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d18444 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41739 (p : Pattern) (ha : d18450 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18342 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41731 q ha hb
    | true =>
      simp only [d18342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41725 q ha hb
  have h2 (q : Pattern) (ha : d18343 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18344 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18352 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41725 q ha hb
    | true =>
      simp only [d18352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41733 q ha hb
  have h5 (q : Pattern) (ha : d18353 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18354 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d18355 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18445 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41725 q ha hb
    | true =>
      simp only [d18445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41738 q ha hb
  have h9 (q : Pattern) (ha : d18446 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18447 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d18448 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d18449 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d18450 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d18450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro41740 (p : Pattern) (ha : d18456 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18451 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41739 q ha hb
    | true =>
      simp only [d18451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18452 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18453 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18454 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18455 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18456 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41741 (p : Pattern) (ha : d129410 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18385 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41736 q ha hb
    | true =>
      simp only [d18385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41737 q ha hb
  have h2 (q : Pattern) (ha : d129406 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d18457 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41740 q ha hb
    | true =>
      simp only [d18457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18458 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d18458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129407 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129408 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129409 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129410 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41742 (p : Pattern) (ha : d129416 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129411 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41741 q ha hb
  have h2 (q : Pattern) (ha : d18474 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d18474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41729 q ha hb
  have h3 (q : Pattern) (ha : d129412 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129413 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129414 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129415 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d129416 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro41743 (p : Pattern) (ha : d129422 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129417 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41742 q ha hb
  have h2 (q : Pattern) (ha : d129418 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129419 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129420 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129421 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129422 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41744 (p : Pattern) (ha : d129428 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d129345 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d129345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41657 q ha hb
    | true =>
      simp only [d129345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41670 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d129363 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d129363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41686 q ha hb
  have h3 (q : Pattern) (ha : d129364 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d129364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129382 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d129382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41705 q ha hb
  have h5 (q : Pattern) (ha : d129383 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d129383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129384 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d129384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129402 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d129402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41724 q ha hb
  have h8 (q : Pattern) (ha : d129403 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d129403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d129404 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d129404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d129405 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d129405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d129405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d129423 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d129423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41743 q ha hb
  have h12 (q : Pattern) (ha : d129424 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d129424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d129425 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d129425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d129426 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d129426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d129427 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d129427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d129427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d129428 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d129428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d129428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro41745 (p : Pattern) (ha : d129434 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129429 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d129429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41744 q ha hb
    | true =>
      simp only [d129429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d129430 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d129430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129431 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d129431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129432 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d129432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129433 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d129433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129434 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d129434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41746 (p : Pattern) (ha : d129440 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129435 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d129435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41745 q ha hb
    | true =>
      simp only [d129435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d129436 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d129436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129437 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d129437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129438 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d129438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129439 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d129439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129440 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d129440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41747 (p : Pattern) (ha : d129446 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129441 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d129441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41746 q ha hb
    | true =>
      simp only [d129441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d129442 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d129442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129443 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d129443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129444 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d129444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129445 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d129445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129446 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d129446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41748 (p : Pattern) (ha : d129452 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129447 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d129447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41747 q ha hb
    | true =>
      simp only [d129447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d129448 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d129448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129449 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d129449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129450 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d129450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129451 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d129451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129452 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d129452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41749 (p : Pattern) (ha : d129458 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129453 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d129453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41748 q ha hb
    | true =>
      simp only [d129453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d129454 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d129454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129455 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d129455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129456 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d129456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129457 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d129457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129458 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d129458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
end NetHack.Soko22Hazard87
