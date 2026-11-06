import NetHack.Soko22Hazard87.AndIntroBlocks0081
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro20500 (p : Pattern) (ha : d121528 p = 1) (hb : d121820 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d121523 q = 1) (hb : d121815 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d121523, d121815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20499 q ha hb
    | true =>
      simp only [d121523, d121815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d121524 q = 1) (hb : d121816 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d121524, d121816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d121524, d121816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d121525 q = 1) (hb : d121817 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d121525, d121817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d121525, d121817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d121526 q = 1) (hb : d121818 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d121526, d121818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d121526, d121818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d121527 q = 1) (hb : d121819 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d121527, d121819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d121527, d121819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d121528 q = 1) (hb : d121820 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d121528, d121820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d121528, d121820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro20501 (p : Pattern) (ha : d121534 p = 1) (hb : d121826 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d121529 q = 1) (hb : d121821 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d121529, d121821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20500 q ha hb
    | true =>
      simp only [d121529, d121821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d121530 q = 1) (hb : d121822 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d121530, d121822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d121530, d121822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d121531 q = 1) (hb : d121823 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d121531, d121823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d121531, d121823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d121532 q = 1) (hb : d121824 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d121532, d121824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d121532, d121824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d121533 q = 1) (hb : d121825 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d121533, d121825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d121533, d121825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d121534 q = 1) (hb : d121826 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d121534, d121826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d121534, d121826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro20502 (p : Pattern) (ha : d121540 p = 1) (hb : d121832 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d121535 q = 1) (hb : d121827 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d121535, d121827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20501 q ha hb
    | true =>
      simp only [d121535, d121827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d121536 q = 1) (hb : d121828 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d121536, d121828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d121536, d121828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d121537 q = 1) (hb : d121829 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d121537, d121829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d121537, d121829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d121538 q = 1) (hb : d121830 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d121538, d121830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d121538, d121830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d121539 q = 1) (hb : d121831 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d121539, d121831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d121539, d121831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d121540 q = 1) (hb : d121832 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d121540, d121832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d121540, d121832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro20503 (p : Pattern) (ha : d121546 p = 1) (hb : d121838 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d121541 q = 1) (hb : d121833 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d121541, d121833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20502 q ha hb
    | true =>
      simp only [d121541, d121833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d121542 q = 1) (hb : d121834 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d121542, d121834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d121542, d121834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d121543 q = 1) (hb : d121835 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d121543, d121835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d121543, d121835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d121544 q = 1) (hb : d121836 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d121544, d121836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d121544, d121836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d121545 q = 1) (hb : d121837 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d121545, d121837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d121545, d121837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d121546 q = 1) (hb : d121838 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d121546, d121838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d121546, d121838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro20504 (p : Pattern) (ha : d121552 p = 1) (hb : d121844 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d121547 q = 1) (hb : d121839 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d121547, d121839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20503 q ha hb
    | true =>
      simp only [d121547, d121839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d121548 q = 1) (hb : d121840 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d121548, d121840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d121548, d121840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d121549 q = 1) (hb : d121841 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d121549, d121841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d121549, d121841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d121550 q = 1) (hb : d121842 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d121550, d121842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d121550, d121842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d121551 q = 1) (hb : d121843 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d121551, d121843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d121551, d121843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d121552 q = 1) (hb : d121844 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d121552, d121844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d121552, d121844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro20505 (p : Pattern) (ha : d121558 p = 1) (hb : d121850 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d121553 q = 1) (hb : d121845 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d121553, d121845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20504 q ha hb
    | true =>
      simp only [d121553, d121845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d121554 q = 1) (hb : d121846 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d121554, d121846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d121554, d121846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d121555 q = 1) (hb : d121847 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d121555, d121847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d121555, d121847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d121556 q = 1) (hb : d121848 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d121556, d121848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d121556, d121848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d121557 q = 1) (hb : d121849 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d121557, d121849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d121557, d121849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d121558 q = 1) (hb : d121850 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d121558, d121850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d121558, d121850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro20506 (p : Pattern) (ha : d121564 p = 1) (hb : d121856 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d121559 q = 1) (hb : d121851 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d121559, d121851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20505 q ha hb
    | true =>
      simp only [d121559, d121851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d121560 q = 1) (hb : d121852 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d121560, d121852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d121560, d121852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d121561 q = 1) (hb : d121853 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d121561, d121853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d121561, d121853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d121562 q = 1) (hb : d121854 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d121562, d121854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d121562, d121854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d121563 q = 1) (hb : d121855 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d121563, d121855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d121563, d121855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d121564 q = 1) (hb : d121856 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d121564, d121856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d121564, d121856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro20507 (p : Pattern) (ha : d8238 p = 1) (hb : d92315 p = 1) : d111667 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6740 q = 1) (hb : d92315 q = 1) : d482 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6740, d482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13976 q ha hb
    | true =>
      simp only [d6740, d482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6741 q = 1) (hb : d92315 q = 1) : d483 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6741, d483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6741, d483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d92315 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8235 q = 1) (hb : d92315 q = 1) : d111664 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8235, d111664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8235, d111664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8236 q = 1) (hb : d92315 q = 1) : d111665 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8236, d111665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8236, d111665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8237 q = 1) (hb : d92315 q = 1) : d111666 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8237, d111666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8237, d111666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8238 q = 1) (hb : d92315 q = 1) : d111667 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8238, d111667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8238, d111667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro20508 (p : Pattern) (ha : d92315 p = 1) (hb : d94191 p = 1) : d111673 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120 q = 1) (hb : d92315 q = 1) : d120 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d126 q = 1) (hb : d92315 q = 1) : d126 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d42 q = 1) (hb : d92315 q = 1) : d42 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8239 q = 1) (hb : d92315 q = 1) : d111668 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8239, d111668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20507 q ha hb
    | true =>
      simp only [d8239, d111668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d94187 q = 1) : d111669 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94187, d111669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d94187, d111669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d92315 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d92315 q = 1) (hb : d94188 q = 1) : d111670 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94188, d111670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94188, d111670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d92315 q = 1) (hb : d94189 q = 1) : d111671 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94189, d111671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d94189, d111671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92315 q = 1) (hb : d94190 q = 1) : d111672 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94190, d111672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94190, d111672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d92315 q = 1) (hb : d94191 q = 1) : d111673 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94191, d111673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94191, d111673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro20509 (p : Pattern) (ha : d8245 p = 1) (hb : d92315 p = 1) : d111674 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6740 q = 1) (hb : d92315 q = 1) : d482 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6740, d482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13976 q ha hb
    | true =>
      simp only [d6740, d482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6741 q = 1) (hb : d92315 q = 1) : d483 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6741, d483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6741, d483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d92315 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8235 q = 1) (hb : d92315 q = 1) : d111664 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8235, d111664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8235, d111664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8236 q = 1) (hb : d92315 q = 1) : d111665 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8236, d111665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8236, d111665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8237 q = 1) (hb : d92315 q = 1) : d111666 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8237, d111666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8237, d111666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8245 q = 1) (hb : d92315 q = 1) : d111674 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8245, d111674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8245, d111674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro20510 (p : Pattern) (ha : d92315 p = 1) (hb : d94196 p = 1) : d111680 p = 1 := by
  have h0 (q : Pattern) (ha : d120 q = 1) (hb : d92315 q = 1) : d120 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d126 q = 1) (hb : d92315 q = 1) : d126 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42 q = 1) (hb : d92315 q = 1) : d42 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8239 q = 1) (hb : d92315 q = 1) : d111668 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8239, d111668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20507 q ha hb
    | true =>
      simp only [d8239, d111668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d94187 q = 1) : d111669 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94187, d111669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d94187, d111669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d92315 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d92315 q = 1) (hb : d94188 q = 1) : d111670 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94188, d111670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94188, d111670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d92315 q = 1) (hb : d94189 q = 1) : d111671 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94189, d111671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94189, d111671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92315 q = 1) (hb : d94190 q = 1) : d111672 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94190, d111672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94190, d111672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d198 q = 1) (hb : d92315 q = 1) : d198 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d202 q = 1) (hb : d92315 q = 1) : d202 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d49 q = 1) (hb : d92315 q = 1) : d49 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d8246 q = 1) (hb : d92315 q = 1) : d111675 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8246, d111675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20509 q ha hb
    | true =>
      simp only [d8246, d111675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d92315 q = 1) (hb : d94192 q = 1) : d111676 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94192, d111676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d94192, d111676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h15 (q : Pattern) (ha : d51 q = 1) (hb : d92315 q = 1) : d51 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d92315 q = 1) (hb : d94193 q = 1) : d111677 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94193, d111677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d94193, d111677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d92315 q = 1) (hb : d94194 q = 1) : d111678 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94194, d111678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d94194, d111678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d92315 q = 1) (hb : d94195 q = 1) : d111679 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94195, d111679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d94195, d111679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d92315 q = 1) (hb : d94196 q = 1) : d111680 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94196, d111680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94196, d111680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro20511 (p : Pattern) (ha : d92315 p = 1) (hb : d94203 p = 1) : d111687 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d92315 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8246 q = 1) (hb : d92315 q = 1) : d111675 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8246, d111675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20509 q ha hb
    | true =>
      simp only [d8246, d111675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92315 q = 1) (hb : d94192 q = 1) : d111676 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94192, d111676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d94192, d111676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d92315 q = 1) : d51 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d94193 q = 1) : d111677 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94193, d111677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94193, d111677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d94201 q = 1) : d111685 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94201, d111685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94201, d111685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92315 q = 1) (hb : d94202 q = 1) : d111686 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94202, d111686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94202, d111686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92315 q = 1) (hb : d94203 q = 1) : d111687 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94203, d111687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94203, d111687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20512 (p : Pattern) (ha : d8267 p = 1) (hb : d92315 p = 1) : d111696 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6773 q = 1) (hb : d92315 q = 1) : d684 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6773, d684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13986 q ha hb
    | true =>
      simp only [d6773, d684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6774 q = 1) (hb : d92315 q = 1) : d685 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6774, d685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6774, d685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79 q = 1) (hb : d92315 q = 1) : d79 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8264 q = 1) (hb : d92315 q = 1) : d111693 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8264, d111693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8264, d111693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8265 q = 1) (hb : d92315 q = 1) : d111694 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8265, d111694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8265, d111694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8266 q = 1) (hb : d92315 q = 1) : d111695 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8266, d111695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8266, d111695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8267 q = 1) (hb : d92315 q = 1) : d111696 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8267, d111696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8267, d111696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro20513 (p : Pattern) (ha : d92315 p = 1) (hb : d94213 p = 1) : d111702 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d92315 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8268 q = 1) (hb : d92315 q = 1) : d111697 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8268, d111697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20512 q ha hb
    | true =>
      simp only [d8268, d111697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92315 q = 1) (hb : d94209 q = 1) : d111698 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94209, d111698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d94209, d111698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d92315 q = 1) : d85 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d94210 q = 1) : d111699 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94210, d111699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94210, d111699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d94211 q = 1) : d111700 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94211, d111700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94211, d111700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92315 q = 1) (hb : d94212 q = 1) : d111701 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94212, d111701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94212, d111701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92315 q = 1) (hb : d94213 q = 1) : d111702 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94213, d111702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94213, d111702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20514 (p : Pattern) (ha : d92315 p = 1) (hb : d94219 p = 1) : d111708 p = 1 := by
  have h0 (q : Pattern) (ha : d114 q = 1) (hb : d92315 q = 1) : d114 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92315 q = 1) (hb : d94197 q = 1) : d111681 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94197, d111681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20508 q ha hb
    | true =>
      simp only [d94197, d111681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20510 q ha hb
  have h2 (q : Pattern) (ha : d214 q = 1) (hb : d92315 q = 1) : d214 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d92315 q = 1) (hb : d94198 q = 1) : d111682 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94198, d111682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94198, d111682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d94199 q = 1) : d111683 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94199, d111683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94199, d111683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d94200 q = 1) : d111684 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94200, d111684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94200, d111684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92315 q = 1) (hb : d94204 q = 1) : d111688 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94204, d111688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d94204, d111688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20511 q ha hb
  have h8 (q : Pattern) (ha : d92315 q = 1) (hb : d94205 q = 1) : d111689 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94205, d111689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94205, d111689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h9 (q : Pattern) (ha : d92315 q = 1) (hb : d94206 q = 1) : d111690 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94206, d111690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94206, d111690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h10 (q : Pattern) (ha : d92315 q = 1) (hb : d94207 q = 1) : d111691 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94207, d111691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94207, d111691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d92315 q = 1) (hb : d94208 q = 1) : d111692 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94208, d111692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94208, d111692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d92315 q = 1) (hb : d94214 q = 1) : d111703 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94214, d111703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d94214, d111703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20513 q ha hb
  have h13 (q : Pattern) (ha : d92315 q = 1) (hb : d94215 q = 1) : d111704 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94215, d111704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d94215, d111704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h14 (q : Pattern) (ha : d92315 q = 1) (hb : d94216 q = 1) : d111705 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94216, d111705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94216, d111705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h15 (q : Pattern) (ha : d92315 q = 1) (hb : d94217 q = 1) : d111706 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94217, d111706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d94217, d111706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h16 (q : Pattern) (ha : d92315 q = 1) (hb : d94218 q = 1) : d111707 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94218, d111707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d94218, d111707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d92315 q = 1) (hb : d94219 q = 1) : d111708 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94219, d111708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94219, d111708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro20515 (p : Pattern) (ha : d8289 p = 1) (hb : d92315 p = 1) : d111718 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d92315 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8239 q = 1) (hb : d92315 q = 1) : d111668 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8239, d111668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20507 q ha hb
    | true =>
      simp only [d8239, d111668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8285 q = 1) (hb : d92315 q = 1) : d111714 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8285, d111714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8285, d111714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8286 q = 1) (hb : d92315 q = 1) : d111715 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8286, d111715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8286, d111715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8287 q = 1) (hb : d92315 q = 1) : d111716 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8287, d111716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8287, d111716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8288 q = 1) (hb : d92315 q = 1) : d111717 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8288, d111717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8288, d111717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8289 q = 1) (hb : d92315 q = 1) : d111718 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8289, d111718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8289, d111718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro20516 (p : Pattern) (ha : d8296 p = 1) (hb : d92315 p = 1) : d111725 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d92315 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8239 q = 1) (hb : d92315 q = 1) : d111668 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8239, d111668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20507 q ha hb
    | true =>
      simp only [d8239, d111668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8285 q = 1) (hb : d92315 q = 1) : d111714 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8285, d111714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8285, d111714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8286 q = 1) (hb : d92315 q = 1) : d111715 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8286, d111715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8286, d111715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8287 q = 1) (hb : d92315 q = 1) : d111716 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8287, d111716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8287, d111716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8288 q = 1) (hb : d92315 q = 1) : d111717 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8288, d111717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8288, d111717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d49 q = 1) (hb : d92315 q = 1) : d49 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d8246 q = 1) (hb : d92315 q = 1) : d111675 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8246, d111675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20509 q ha hb
    | true =>
      simp only [d8246, d111675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d8292 q = 1) (hb : d92315 q = 1) : d111721 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8292, d111721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8292, d111721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d8293 q = 1) (hb : d92315 q = 1) : d111722 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8293, d111722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d8293, d111722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d8294 q = 1) (hb : d92315 q = 1) : d111723 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8294, d111723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8294, d111723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d8295 q = 1) (hb : d92315 q = 1) : d111724 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8295, d111724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8295, d111724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d8296 q = 1) (hb : d92315 q = 1) : d111725 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8296, d111725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8296, d111725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro20517 (p : Pattern) (ha : d8363 p = 1) (hb : d92315 p = 1) : d111770 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d92315 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8239 q = 1) (hb : d92315 q = 1) : d111668 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8239, d111668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20507 q ha hb
    | true =>
      simp only [d8239, d111668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8285 q = 1) (hb : d92315 q = 1) : d111714 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8285, d111714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8285, d111714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8286 q = 1) (hb : d92315 q = 1) : d111715 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8286, d111715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8286, d111715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8287 q = 1) (hb : d92315 q = 1) : d111716 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8287, d111716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8287, d111716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8288 q = 1) (hb : d92315 q = 1) : d111717 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8288, d111717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8288, d111717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d103 q = 1) (hb : d92315 q = 1) : d103 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d8363 q = 1) (hb : d92315 q = 1) : d111770 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8363, d111770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8363, d111770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20518 (p : Pattern) (ha : d8301 p = 1) (hb : d92315 p = 1) : d111730 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6740 q = 1) (hb : d92315 q = 1) : d482 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6740, d482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13976 q ha hb
    | true =>
      simp only [d6740, d482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6741 q = 1) (hb : d92315 q = 1) : d483 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6741, d483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6741, d483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d92315 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8235 q = 1) (hb : d92315 q = 1) : d111664 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8235, d111664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8235, d111664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8236 q = 1) (hb : d92315 q = 1) : d111665 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8236, d111665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8236, d111665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8300 q = 1) (hb : d92315 q = 1) : d111729 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8300, d111729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8300, d111729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8301 q = 1) (hb : d92315 q = 1) : d111730 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8301, d111730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8301, d111730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro20519 (p : Pattern) (ha : d8308 p = 1) (hb : d92315 p = 1) : d111737 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6740 q = 1) (hb : d92315 q = 1) : d482 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6740, d482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13976 q ha hb
    | true =>
      simp only [d6740, d482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6741 q = 1) (hb : d92315 q = 1) : d483 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6741, d483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6741, d483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d92315 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8235 q = 1) (hb : d92315 q = 1) : d111664 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8235, d111664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8235, d111664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8306 q = 1) (hb : d92315 q = 1) : d111735 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8306, d111735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8306, d111735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8307 q = 1) (hb : d92315 q = 1) : d111736 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8307, d111736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8307, d111736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8308 q = 1) (hb : d92315 q = 1) : d111737 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8308, d111737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8308, d111737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro20520 (p : Pattern) (ha : d8313 p = 1) (hb : d92315 p = 1) : d98845 p = 1 := by
  have h0 (q : Pattern) (ha : d6797 q = 1) (hb : d92313 q = 1) : d6797 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d475 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8312 q = 1) (hb : d92315 q = 1) : d98844 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8312, d92315, d98844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8312, d92315, d98844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8313 q = 1) (hb : d92315 q = 1) : d98845 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8313, d98845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8313, d98845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro20521 (p : Pattern) (ha : d8319 p = 1) (hb : d92315 p = 1) : d111744 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8314 q = 1) (hb : d92315 q = 1) : d98846 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8314, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20520 q ha hb
    | true =>
      simp only [d8314, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8315 q = 1) (hb : d92315 q = 1) : d98847 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8315, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8315, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6740 q = 1) (hb : d92315 q = 1) : d482 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6740, d482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13976 q ha hb
    | true =>
      simp only [d6740, d482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6741 q = 1) (hb : d92315 q = 1) : d483 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6741, d483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6741, d483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8316 q = 1) (hb : d92315 q = 1) : d111741 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8316, d111741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8316, d111741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8317 q = 1) (hb : d92315 q = 1) : d111742 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8317, d111742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8317, d111742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8318 q = 1) (hb : d92315 q = 1) : d111743 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8318, d111743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8318, d111743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8319 q = 1) (hb : d92315 q = 1) : d111744 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8319, d111744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8319, d111744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20522 (p : Pattern) (ha : d8334 p = 1) (hb : d92315 p = 1) : d491 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6740 q = 1) (hb : d92315 q = 1) : d482 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6740, d482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13976 q ha hb
    | true =>
      simp only [d6740, d482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6741 q = 1) (hb : d92315 q = 1) : d483 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6741, d483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6741, d483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8331 q = 1) (hb : d92315 q = 1) : d488 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8331, d488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8331, d488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8332 q = 1) (hb : d92315 q = 1) : d489 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8332, d489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8332, d489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8333 q = 1) (hb : d92315 q = 1) : d490 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8333, d490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8333, d490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8334 q = 1) (hb : d92315 q = 1) : d491 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8334, d491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8334, d491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20523 (p : Pattern) (ha : d92315 p = 1) (hb : d94229 p = 1) : d111751 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d92315 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8302 q = 1) (hb : d92315 q = 1) : d111731 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8302, d111731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20518 q ha hb
    | true =>
      simp only [d8302, d111731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8303 q = 1) (hb : d92315 q = 1) : d111732 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8303, d111732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8303, d111732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8304 q = 1) (hb : d92315 q = 1) : d111733 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8304, d111733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8304, d111733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8305 q = 1) (hb : d92315 q = 1) : d111734 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8305, d111734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8305, d111734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d92315 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d8309 q = 1) (hb : d92315 q = 1) : d111738 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8309, d111738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20519 q ha hb
    | true =>
      simp only [d8309, d111738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8310 q = 1) (hb : d92315 q = 1) : d111739 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8310, d111739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8310, d111739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d8311 q = 1) (hb : d92315 q = 1) : d111740 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8311, d111740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d8311, d111740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d8320 q = 1) (hb : d92315 q = 1) : d111745 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8320, d111745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20521 q ha hb
    | true =>
      simp only [d8320, d111745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20507 q ha hb
  have h11 (q : Pattern) (ha : d92315 q = 1) (hb : d94225 q = 1) : d111746 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94225, d111746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d94225, d111746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d8335 q = 1) (hb : d92315 q = 1) : d633 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8335, d633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20522 q ha hb
    | true =>
      simp only [d8335, d633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d8336 q = 1) (hb : d92315 q = 1) : d111747 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8336, d111747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d8336, d111747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d92315 q = 1) (hb : d94226 q = 1) : d111748 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94226, d111748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94226, d111748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d92315 q = 1) (hb : d94227 q = 1) : d111749 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94227, d111749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d94227, d111749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d92315 q = 1) (hb : d94228 q = 1) : d111750 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94228, d111750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d94228, d111750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d92315 q = 1) (hb : d94229 q = 1) : d111751 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94229, d111751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94229, d111751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro20524 (p : Pattern) (ha : d8341 p = 1) (hb : d92315 p = 1) : d111752 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6740 q = 1) (hb : d92315 q = 1) : d482 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6740, d482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13976 q ha hb
    | true =>
      simp only [d6740, d482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6741 q = 1) (hb : d92315 q = 1) : d483 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6741, d483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6741, d483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d92315 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8235 q = 1) (hb : d92315 q = 1) : d111664 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8235, d111664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8235, d111664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8236 q = 1) (hb : d92315 q = 1) : d111665 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8236, d111665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8236, d111665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8300 q = 1) (hb : d92315 q = 1) : d111729 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8300, d111729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8300, d111729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8341 q = 1) (hb : d92315 q = 1) : d111752 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8341, d111752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8341, d111752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro20525 (p : Pattern) (ha : d8346 p = 1) (hb : d92315 p = 1) : d111757 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6740 q = 1) (hb : d92315 q = 1) : d482 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6740, d482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13976 q ha hb
    | true =>
      simp only [d6740, d482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6741 q = 1) (hb : d92315 q = 1) : d483 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6741, d483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6741, d483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d92315 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8235 q = 1) (hb : d92315 q = 1) : d111664 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8235, d111664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8235, d111664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8306 q = 1) (hb : d92315 q = 1) : d111735 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8306, d111735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8306, d111735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8307 q = 1) (hb : d92315 q = 1) : d111736 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8307, d111736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8307, d111736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8346 q = 1) (hb : d92315 q = 1) : d111757 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8346, d111757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8346, d111757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro20526 (p : Pattern) (ha : d8350 p = 1) (hb : d92315 p = 1) : d111761 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8314 q = 1) (hb : d92315 q = 1) : d98846 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8314, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20520 q ha hb
    | true =>
      simp only [d8314, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8315 q = 1) (hb : d92315 q = 1) : d98847 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8315, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8315, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6740 q = 1) (hb : d92315 q = 1) : d482 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6740, d482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13976 q ha hb
    | true =>
      simp only [d6740, d482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6741 q = 1) (hb : d92315 q = 1) : d483 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6741, d483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6741, d483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8316 q = 1) (hb : d92315 q = 1) : d111741 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8316, d111741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8316, d111741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8317 q = 1) (hb : d92315 q = 1) : d111742 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8317, d111742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8317, d111742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8318 q = 1) (hb : d92315 q = 1) : d111743 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8318, d111743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8318, d111743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8350 q = 1) (hb : d92315 q = 1) : d111761 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8350, d111761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8350, d111761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro20527 (p : Pattern) (ha : d8355 p = 1) (hb : d92315 p = 1) : d501 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6740 q = 1) (hb : d92315 q = 1) : d482 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6740, d482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13976 q ha hb
    | true =>
      simp only [d6740, d482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6741 q = 1) (hb : d92315 q = 1) : d483 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6741, d483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6741, d483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8331 q = 1) (hb : d92315 q = 1) : d488 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8331, d488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8331, d488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8332 q = 1) (hb : d92315 q = 1) : d489 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8332, d489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8332, d489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8333 q = 1) (hb : d92315 q = 1) : d490 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8333, d490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8333, d490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8355 q = 1) (hb : d92315 q = 1) : d501 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8355, d501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8355, d501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro20528 (p : Pattern) (ha : d92315 p = 1) (hb : d94234 p = 1) : d111768 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d92315 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8302 q = 1) (hb : d92315 q = 1) : d111731 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8302, d111731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20518 q ha hb
    | true =>
      simp only [d8302, d111731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8303 q = 1) (hb : d92315 q = 1) : d111732 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8303, d111732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8303, d111732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8304 q = 1) (hb : d92315 q = 1) : d111733 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8304, d111733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8304, d111733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8305 q = 1) (hb : d92315 q = 1) : d111734 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8305, d111734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8305, d111734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d92315 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d8309 q = 1) (hb : d92315 q = 1) : d111738 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8309, d111738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20519 q ha hb
    | true =>
      simp only [d8309, d111738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8310 q = 1) (hb : d92315 q = 1) : d111739 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8310, d111739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8310, d111739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d8311 q = 1) (hb : d92315 q = 1) : d111740 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8311, d111740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d8311, d111740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d8320 q = 1) (hb : d92315 q = 1) : d111745 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8320, d111745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20521 q ha hb
    | true =>
      simp only [d8320, d111745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20507 q ha hb
  have h11 (q : Pattern) (ha : d92315 q = 1) (hb : d94225 q = 1) : d111746 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94225, d111746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d94225, d111746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d8335 q = 1) (hb : d92315 q = 1) : d633 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8335, d633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20522 q ha hb
    | true =>
      simp only [d8335, d633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d8336 q = 1) (hb : d92315 q = 1) : d111747 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8336, d111747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d8336, d111747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d92315 q = 1) (hb : d94226 q = 1) : d111748 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94226, d111748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94226, d111748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d92315 q = 1) (hb : d94227 q = 1) : d111749 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94227, d111749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d94227, d111749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d92315 q = 1) (hb : d94228 q = 1) : d111750 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94228, d111750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d94228, d111750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d194 q = 1) (hb : d92315 q = 1) : d194 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d8342 q = 1) (hb : d92315 q = 1) : d111753 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8342, d111753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20524 q ha hb
    | true =>
      simp only [d8342, d111753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d8343 q = 1) (hb : d92315 q = 1) : d111754 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8343, d111754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8343, d111754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d8344 q = 1) (hb : d92315 q = 1) : d111755 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8344, d111755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d8344, d111755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d8345 q = 1) (hb : d92315 q = 1) : d111756 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8345, d111756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8345, d111756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d199 q = 1) (hb : d92315 q = 1) : d199 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d8347 q = 1) (hb : d92315 q = 1) : d111758 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8347, d111758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20525 q ha hb
    | true =>
      simp only [d8347, d111758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d8348 q = 1) (hb : d92315 q = 1) : d111759 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8348, d111759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8348, d111759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d8349 q = 1) (hb : d92315 q = 1) : d111760 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8349, d111760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d8349, d111760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d8351 q = 1) (hb : d92315 q = 1) : d111762 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8351, d111762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20526 q ha hb
    | true =>
      simp only [d8351, d111762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20509 q ha hb
  have h27 (q : Pattern) (ha : d92315 q = 1) (hb : d94230 q = 1) : d111763 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94230, d111763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q hb ha
    | true =>
      simp only [d94230, d111763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d8356 q = 1) (hb : d92315 q = 1) : d639 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8356, d639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20527 q ha hb
    | true =>
      simp only [d8356, d639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d8357 q = 1) (hb : d92315 q = 1) : d111764 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8357, d111764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d8357, d111764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d92315 q = 1) (hb : d94231 q = 1) : d111765 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94231, d111765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d94231, d111765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q hb ha
  have h31 (q : Pattern) (ha : d92315 q = 1) (hb : d94232 q = 1) : d111766 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94232, d111766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
    | true =>
      simp only [d94232, d111766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d92315 q = 1) (hb : d94233 q = 1) : d111767 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94233, d111767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d94233, d111767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d92315 q = 1) (hb : d94234 q = 1) : d111768 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94234, d111768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d94234, d111768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro20529 (p : Pattern) (ha : d92315 p = 1) (hb : d94241 p = 1) : d111777 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8351 q = 1) (hb : d92315 q = 1) : d111762 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8351, d111762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20526 q ha hb
    | true =>
      simp only [d8351, d111762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20509 q ha hb
  have h2 (q : Pattern) (ha : d92315 q = 1) (hb : d94230 q = 1) : d111763 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94230, d111763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94230, d111763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d8356 q = 1) (hb : d92315 q = 1) : d639 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8356, d639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20527 q ha hb
    | true =>
      simp only [d8356, d639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8357 q = 1) (hb : d92315 q = 1) : d111764 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8357, d111764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8357, d111764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d94231 q = 1) : d111765 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94231, d111765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94231, d111765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d94239 q = 1) : d111775 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94239, d111775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94239, d111775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92315 q = 1) (hb : d94240 q = 1) : d111776 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94240, d111776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94240, d111776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92315 q = 1) (hb : d94241 q = 1) : d111777 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94241, d111777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94241, d111777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20530 (p : Pattern) (ha : d8377 p = 1) (hb : d92315 p = 1) : d98878 p = 1 := by
  have h0 (q : Pattern) (ha : d6843 q = 1) (hb : d92313 q = 1) : d6843 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d673 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8376 q = 1) (hb : d92315 q = 1) : d98877 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8376, d92315, d98877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8376, d92315, d98877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8377 q = 1) (hb : d92315 q = 1) : d98878 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8377, d98878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8377, d98878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro20531 (p : Pattern) (ha : d8383 p = 1) (hb : d92315 p = 1) : d111786 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8378 q = 1) (hb : d92315 q = 1) : d98879 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8378, d98879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20530 q ha hb
    | true =>
      simp only [d8378, d98879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8379 q = 1) (hb : d92315 q = 1) : d98880 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8379, d98880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8379, d98880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6773 q = 1) (hb : d92315 q = 1) : d684 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6773, d684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13986 q ha hb
    | true =>
      simp only [d6773, d684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6774 q = 1) (hb : d92315 q = 1) : d685 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6774, d685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6774, d685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8380 q = 1) (hb : d92315 q = 1) : d111783 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8380, d111783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8380, d111783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8381 q = 1) (hb : d92315 q = 1) : d111784 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8381, d111784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8381, d111784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8382 q = 1) (hb : d92315 q = 1) : d111785 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8382, d111785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8382, d111785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8383 q = 1) (hb : d92315 q = 1) : d111786 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8383, d111786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8383, d111786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro20532 (p : Pattern) (ha : d8398 p = 1) (hb : d92315 p = 1) : d730 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6773 q = 1) (hb : d92315 q = 1) : d684 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6773, d684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13986 q ha hb
    | true =>
      simp only [d6773, d684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6774 q = 1) (hb : d92315 q = 1) : d685 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6774, d685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6774, d685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8395 q = 1) (hb : d92315 q = 1) : d727 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8395, d727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8395, d727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8396 q = 1) (hb : d92315 q = 1) : d728 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8396, d728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8396, d728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8397 q = 1) (hb : d92315 q = 1) : d729 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8397, d729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8397, d729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8398 q = 1) (hb : d92315 q = 1) : d730 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8398, d730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8398, d730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro20533 (p : Pattern) (ha : d92315 p = 1) (hb : d94251 p = 1) : d111793 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8384 q = 1) (hb : d92315 q = 1) : d111787 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8384, d111787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20531 q ha hb
    | true =>
      simp only [d8384, d111787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20512 q ha hb
  have h2 (q : Pattern) (ha : d92315 q = 1) (hb : d94247 q = 1) : d111788 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94247, d111788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94247, d111788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d8399 q = 1) (hb : d92315 q = 1) : d731 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8399, d731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20532 q ha hb
    | true =>
      simp only [d8399, d731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8400 q = 1) (hb : d92315 q = 1) : d111789 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8400, d111789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8400, d111789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d94248 q = 1) : d111790 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94248, d111790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94248, d111790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d94249 q = 1) : d111791 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94249, d111791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94249, d111791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92315 q = 1) (hb : d94250 q = 1) : d111792 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94250, d111792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94250, d111792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92315 q = 1) (hb : d94251 q = 1) : d111793 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94251, d111793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94251, d111793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20534 (p : Pattern) (ha : d92315 p = 1) (hb : d94257 p = 1) : d111799 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8290 q = 1) (hb : d92315 q = 1) : d111719 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8290, d111719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8290, d111719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20515 q ha hb
  have h2 (q : Pattern) (ha : d8291 q = 1) (hb : d92315 q = 1) : d111720 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8291, d111720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8291, d111720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8297 q = 1) (hb : d92315 q = 1) : d111726 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8297, d111726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20515 q ha hb
    | true =>
      simp only [d8297, d111726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20516 q ha hb
  have h4 (q : Pattern) (ha : d8298 q = 1) (hb : d92315 q = 1) : d111727 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8298, d111727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8298, d111727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8299 q = 1) (hb : d92315 q = 1) : d111728 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d8299, d111728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8299, d111728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d94235 q = 1) : d111769 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94235, d111769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20523 q ha hb
    | true =>
      simp only [d94235, d111769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20528 q ha hb
  have h7 (q : Pattern) (ha : d111 q = 1) (hb : d92315 q = 1) : d111 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d8364 q = 1) (hb : d92315 q = 1) : d111771 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8364, d111771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20517 q ha hb
    | true =>
      simp only [d8364, d111771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92315 q = 1) (hb : d94236 q = 1) : d111772 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94236, d111772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94236, d111772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d92315 q = 1) (hb : d94237 q = 1) : d111773 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94237, d111773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94237, d111773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d92315 q = 1) (hb : d94238 q = 1) : d111774 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94238, d111774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d94238, d111774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d92315 q = 1) (hb : d94242 q = 1) : d111778 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94242, d111778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94242, d111778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20529 q ha hb
  have h13 (q : Pattern) (ha : d407 q = 1) (hb : d92315 q = 1) : d407 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d92315 q = 1) (hb : d94243 q = 1) : d111779 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94243, d111779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d94243, d111779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d92315 q = 1) (hb : d94244 q = 1) : d111780 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94244, d111780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d94244, d111780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d92315 q = 1) (hb : d94245 q = 1) : d111781 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94245, d111781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d94245, d111781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d92315 q = 1) (hb : d94246 q = 1) : d111782 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94246, d111782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94246, d111782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d92315 q = 1) (hb : d94252 q = 1) : d111794 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94252, d111794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94252, d111794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20533 q ha hb
  have h19 (q : Pattern) (ha : d463 q = 1) (hb : d92315 q = 1) : d463 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d92315 q = 1) (hb : d94253 q = 1) : d111795 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94253, d111795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d94253, d111795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d92315 q = 1) (hb : d94254 q = 1) : d111796 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94254, d111796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d94254, d111796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d92315 q = 1) (hb : d94255 q = 1) : d111797 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94255, d111797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d94255, d111797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d92315 q = 1) (hb : d94256 q = 1) : d111798 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94256, d111798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d94256, d111798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d92315 q = 1) (hb : d94257 q = 1) : d111799 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94257, d111799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d94257, d111799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro20535 (p : Pattern) (ha : d92315 p = 1) (hb : d94263 p = 1) : d111805 p = 1 := by
  have h0 (q : Pattern) (ha : d99 q = 1) (hb : d92315 q = 1) : d99 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d92315 q = 1) (hb : d94220 q = 1) : d111709 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94220, d111709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94220, d111709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20514 q ha hb
  have h3 (q : Pattern) (ha : d92315 q = 1) (hb : d94221 q = 1) : d111710 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94221, d111710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94221, d111710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92315 q = 1) (hb : d94222 q = 1) : d111711 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94222, d111711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94222, d111711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d94223 q = 1) : d111712 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94223, d111712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94223, d111712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d94224 q = 1) : d111713 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94224, d111713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94224, d111713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92315 q = 1) (hb : d94258 q = 1) : d111800 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94258, d111800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94258, d111800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20534 q ha hb
  have h8 (q : Pattern) (ha : d92315 q = 1) (hb : d94259 q = 1) : d111801 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94259, d111801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94259, d111801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92315 q = 1) (hb : d94260 q = 1) : d111802 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94260, d111802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94260, d111802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d92315 q = 1) (hb : d94261 q = 1) : d111803 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94261, d111803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94261, d111803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d92315 q = 1) (hb : d94262 q = 1) : d111804 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94262, d111804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94262, d111804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d92315 q = 1) (hb : d94263 q = 1) : d111805 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94263, d111805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94263, d111805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro20536 (p : Pattern) (ha : d8420 p = 1) (hb : d92315 p = 1) : d111744 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8314 q = 1) (hb : d92315 q = 1) : d98846 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8314, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20520 q ha hb
    | true =>
      simp only [d8314, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8315 q = 1) (hb : d92315 q = 1) : d98847 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8315, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8315, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d483 q = 1) (hb : d92315 q = 1) : d483 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8417 q = 1) (hb : d92315 q = 1) : d111741 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8417, d111741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8417, d111741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8418 q = 1) (hb : d92315 q = 1) : d111742 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8418, d111742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8418, d111742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8419 q = 1) (hb : d92315 q = 1) : d111743 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8419, d111743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8419, d111743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8420 q = 1) (hb : d92315 q = 1) : d111744 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8420, d111744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8420, d111744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro20537 (p : Pattern) (ha : d8426 p = 1) (hb : d92315 p = 1) : d111811 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d491 q = 1) (hb : d92315 q = 1) : d491 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8421 q = 1) (hb : d92315 q = 1) : d111806 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8421, d111806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20536 q ha hb
    | true =>
      simp only [d8421, d111806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8422 q = 1) (hb : d92315 q = 1) : d111807 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8422, d111807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8422, d111807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8423 q = 1) (hb : d92315 q = 1) : d111808 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8423, d111808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8423, d111808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8424 q = 1) (hb : d92315 q = 1) : d111809 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8424, d111809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8424, d111809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8425 q = 1) (hb : d92315 q = 1) : d111810 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8425, d111810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8425, d111810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8426 q = 1) (hb : d92315 q = 1) : d111811 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8426, d111811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8426, d111811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro20538 (p : Pattern) (ha : d8429 p = 1) (hb : d92315 p = 1) : d111761 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8314 q = 1) (hb : d92315 q = 1) : d98846 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8314, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20520 q ha hb
    | true =>
      simp only [d8314, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8315 q = 1) (hb : d92315 q = 1) : d98847 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8315, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8315, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d483 q = 1) (hb : d92315 q = 1) : d483 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8417 q = 1) (hb : d92315 q = 1) : d111741 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8417, d111741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8417, d111741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8418 q = 1) (hb : d92315 q = 1) : d111742 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8418, d111742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8418, d111742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8419 q = 1) (hb : d92315 q = 1) : d111743 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8419, d111743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8419, d111743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8429 q = 1) (hb : d92315 q = 1) : d111761 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8429, d111761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8429, d111761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro20539 (p : Pattern) (ha : d8435 p = 1) (hb : d92315 p = 1) : d111819 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d491 q = 1) (hb : d92315 q = 1) : d491 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8421 q = 1) (hb : d92315 q = 1) : d111806 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8421, d111806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20536 q ha hb
    | true =>
      simp only [d8421, d111806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8422 q = 1) (hb : d92315 q = 1) : d111807 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8422, d111807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8422, d111807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8423 q = 1) (hb : d92315 q = 1) : d111808 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8423, d111808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8423, d111808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8424 q = 1) (hb : d92315 q = 1) : d111809 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8424, d111809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8424, d111809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8425 q = 1) (hb : d92315 q = 1) : d111810 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8425, d111810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8425, d111810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d501 q = 1) (hb : d92315 q = 1) : d501 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d8430 q = 1) (hb : d92315 q = 1) : d111814 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8430, d111814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20538 q ha hb
    | true =>
      simp only [d8430, d111814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d8431 q = 1) (hb : d92315 q = 1) : d111815 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8431, d111815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8431, d111815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d8432 q = 1) (hb : d92315 q = 1) : d111816 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8432, d111816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d8432, d111816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d8433 q = 1) (hb : d92315 q = 1) : d111817 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8433, d111817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8433, d111817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d8434 q = 1) (hb : d92315 q = 1) : d111818 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8434, d111818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8434, d111818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d8435 q = 1) (hb : d92315 q = 1) : d111819 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8435, d111819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8435, d111819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro20540 (p : Pattern) (ha : d8463 p = 1) (hb : d92315 p = 1) : d111744 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6800 q = 1) (hb : d92315 q = 1) : d98846 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6800, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14000 q ha hb
    | true =>
      simp only [d6800, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6801 q = 1) (hb : d92315 q = 1) : d98847 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6801, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6801, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d483 q = 1) (hb : d92315 q = 1) : d483 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8460 q = 1) (hb : d92315 q = 1) : d111741 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8460, d111741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8460, d111741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8461 q = 1) (hb : d92315 q = 1) : d111742 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8461, d111742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8461, d111742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8462 q = 1) (hb : d92315 q = 1) : d111743 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8462, d111743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8462, d111743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8463 q = 1) (hb : d92315 q = 1) : d111744 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8463, d111744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8463, d111744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro20541 (p : Pattern) (ha : d8514 p = 1) (hb : d92315 p = 1) : d111875 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d491 q = 1) (hb : d92315 q = 1) : d491 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8509 q = 1) (hb : d92315 q = 1) : d111806 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8509, d111806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20540 q ha hb
    | true =>
      simp only [d8509, d111806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8510 q = 1) (hb : d92315 q = 1) : d111807 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8510, d111807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8510, d111807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8511 q = 1) (hb : d92315 q = 1) : d111808 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8511, d111808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8511, d111808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8512 q = 1) (hb : d92315 q = 1) : d111809 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8512, d111809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8512, d111809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8513 q = 1) (hb : d92315 q = 1) : d111810 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8513, d111810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8513, d111810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d637 q = 1) (hb : d92315 q = 1) : d637 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d8514 q = 1) (hb : d92315 q = 1) : d111875 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8514, d111875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8514, d111875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20542 (p : Pattern) (ha : d8440 p = 1) (hb : d92315 p = 1) : d111824 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8314 q = 1) (hb : d92315 q = 1) : d98846 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8314, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20520 q ha hb
    | true =>
      simp only [d8314, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8315 q = 1) (hb : d92315 q = 1) : d98847 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8315, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8315, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d483 q = 1) (hb : d92315 q = 1) : d483 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8417 q = 1) (hb : d92315 q = 1) : d111741 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8417, d111741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8417, d111741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8418 q = 1) (hb : d92315 q = 1) : d111742 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8418, d111742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8418, d111742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8439 q = 1) (hb : d92315 q = 1) : d111823 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8439, d111823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8439, d111823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8440 q = 1) (hb : d92315 q = 1) : d111824 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8440, d111824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8440, d111824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro20543 (p : Pattern) (ha : d8447 p = 1) (hb : d92315 p = 1) : d111831 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8314 q = 1) (hb : d92315 q = 1) : d98846 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8314, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20520 q ha hb
    | true =>
      simp only [d8314, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8315 q = 1) (hb : d92315 q = 1) : d98847 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8315, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8315, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d483 q = 1) (hb : d92315 q = 1) : d483 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8417 q = 1) (hb : d92315 q = 1) : d111741 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8417, d111741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8417, d111741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8445 q = 1) (hb : d92315 q = 1) : d111829 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8445, d111829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8445, d111829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8446 q = 1) (hb : d92315 q = 1) : d111830 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8446, d111830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8446, d111830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8447 q = 1) (hb : d92315 q = 1) : d111831 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8447, d111831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8447, d111831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro20544 (p : Pattern) (ha : d8453 p = 1) (hb : d92315 p = 1) : d111836 p = 1 := by
  have h0 (q : Pattern) (ha : d8451 q = 1) (hb : d92313 q = 1) : d8451 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6797 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8452 q = 1) (hb : d92315 q = 1) : d111835 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8452, d92315, d111835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8452, d92315, d111835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8453 q = 1) (hb : d92315 q = 1) : d111836 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8453, d111836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8453, d111836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro20545 (p : Pattern) (ha : d8459 p = 1) (hb : d92315 p = 1) : d111842 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8454 q = 1) (hb : d92315 q = 1) : d111837 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8454, d111837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20544 q ha hb
    | true =>
      simp only [d8454, d111837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8455 q = 1) (hb : d92315 q = 1) : d111838 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8455, d111838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8455, d111838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6800 q = 1) (hb : d92315 q = 1) : d98846 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6800, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14000 q ha hb
    | true =>
      simp only [d6800, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6801 q = 1) (hb : d92315 q = 1) : d98847 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6801, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6801, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8456 q = 1) (hb : d92315 q = 1) : d111839 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8456, d111839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8456, d111839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8457 q = 1) (hb : d92315 q = 1) : d111840 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8457, d111840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8457, d111840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8458 q = 1) (hb : d92315 q = 1) : d111841 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8458, d111841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8458, d111841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8459 q = 1) (hb : d92315 q = 1) : d111842 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8459, d111842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8459, d111842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20546 (p : Pattern) (ha : d8479 p = 1) (hb : d92315 p = 1) : d111848 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8314 q = 1) (hb : d92315 q = 1) : d98846 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8314, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20520 q ha hb
    | true =>
      simp only [d8314, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8315 q = 1) (hb : d92315 q = 1) : d98847 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8315, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8315, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8476 q = 1) (hb : d92315 q = 1) : d111845 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8476, d111845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8476, d111845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8477 q = 1) (hb : d92315 q = 1) : d111846 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8477, d111846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8477, d111846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8478 q = 1) (hb : d92315 q = 1) : d111847 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8478, d111847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8478, d111847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8479 q = 1) (hb : d92315 q = 1) : d111848 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8479, d111848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8479, d111848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20547 (p : Pattern) (ha : d92315 p = 1) (hb : d94268 p = 1) : d111854 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d514 q = 1) (hb : d92315 q = 1) : d514 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8441 q = 1) (hb : d92315 q = 1) : d111825 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8441, d111825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20542 q ha hb
    | true =>
      simp only [d8441, d111825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8442 q = 1) (hb : d92315 q = 1) : d111826 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8442, d111826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8442, d111826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8443 q = 1) (hb : d92315 q = 1) : d111827 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8443, d111827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8443, d111827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8444 q = 1) (hb : d92315 q = 1) : d111828 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8444, d111828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8444, d111828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d524 q = 1) (hb : d92315 q = 1) : d524 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d8448 q = 1) (hb : d92315 q = 1) : d111832 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8448, d111832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20543 q ha hb
    | true =>
      simp only [d8448, d111832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8449 q = 1) (hb : d92315 q = 1) : d111833 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8449, d111833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8449, d111833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d8450 q = 1) (hb : d92315 q = 1) : d111834 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8450, d111834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d8450, d111834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d8464 q = 1) (hb : d92315 q = 1) : d111843 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8464, d111843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20545 q ha hb
    | true =>
      simp only [d8464, d111843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20540 q ha hb
  have h11 (q : Pattern) (ha : d92315 q = 1) (hb : d94264 q = 1) : d111844 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94264, d111844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d94264, d111844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d8480 q = 1) (hb : d92315 q = 1) : d111849 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8480, d111849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20546 q ha hb
    | true =>
      simp only [d8480, d111849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d8481 q = 1) (hb : d92315 q = 1) : d111850 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8481, d111850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d8481, d111850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d92315 q = 1) (hb : d94265 q = 1) : d111851 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94265, d111851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94265, d111851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d92315 q = 1) (hb : d94266 q = 1) : d111852 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94266, d111852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d94266, d111852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d92315 q = 1) (hb : d94267 q = 1) : d111853 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94267, d111853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d94267, d111853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d92315 q = 1) (hb : d94268 q = 1) : d111854 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94268, d111854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94268, d111854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro20548 (p : Pattern) (ha : d8486 p = 1) (hb : d92315 p = 1) : d111855 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8314 q = 1) (hb : d92315 q = 1) : d98846 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8314, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20520 q ha hb
    | true =>
      simp only [d8314, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8315 q = 1) (hb : d92315 q = 1) : d98847 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8315, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8315, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d483 q = 1) (hb : d92315 q = 1) : d483 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8417 q = 1) (hb : d92315 q = 1) : d111741 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8417, d111741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8417, d111741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8418 q = 1) (hb : d92315 q = 1) : d111742 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8418, d111742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8418, d111742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8439 q = 1) (hb : d92315 q = 1) : d111823 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8439, d111823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8439, d111823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8486 q = 1) (hb : d92315 q = 1) : d111855 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8486, d111855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8486, d111855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro20549 (p : Pattern) (ha : d8491 p = 1) (hb : d92315 p = 1) : d111860 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8314 q = 1) (hb : d92315 q = 1) : d98846 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8314, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20520 q ha hb
    | true =>
      simp only [d8314, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8315 q = 1) (hb : d92315 q = 1) : d98847 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8315, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8315, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d483 q = 1) (hb : d92315 q = 1) : d483 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8417 q = 1) (hb : d92315 q = 1) : d111741 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8417, d111741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8417, d111741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8445 q = 1) (hb : d92315 q = 1) : d111829 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8445, d111829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8445, d111829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8446 q = 1) (hb : d92315 q = 1) : d111830 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8446, d111830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8446, d111830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8491 q = 1) (hb : d92315 q = 1) : d111860 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8491, d111860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8491, d111860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro20550 (p : Pattern) (ha : d8495 p = 1) (hb : d92315 p = 1) : d111864 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8454 q = 1) (hb : d92315 q = 1) : d111837 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8454, d111837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20544 q ha hb
    | true =>
      simp only [d8454, d111837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8455 q = 1) (hb : d92315 q = 1) : d111838 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8455, d111838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8455, d111838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6800 q = 1) (hb : d92315 q = 1) : d98846 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6800, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14000 q ha hb
    | true =>
      simp only [d6800, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6801 q = 1) (hb : d92315 q = 1) : d98847 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6801, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6801, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8456 q = 1) (hb : d92315 q = 1) : d111839 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8456, d111839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8456, d111839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8457 q = 1) (hb : d92315 q = 1) : d111840 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8457, d111840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8457, d111840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8458 q = 1) (hb : d92315 q = 1) : d111841 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8458, d111841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8458, d111841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8495 q = 1) (hb : d92315 q = 1) : d111864 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8495, d111864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8495, d111864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro20551 (p : Pattern) (ha : d8496 p = 1) (hb : d92315 p = 1) : d111761 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6800 q = 1) (hb : d92315 q = 1) : d98846 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6800, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14000 q ha hb
    | true =>
      simp only [d6800, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6801 q = 1) (hb : d92315 q = 1) : d98847 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6801, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6801, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d483 q = 1) (hb : d92315 q = 1) : d483 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8460 q = 1) (hb : d92315 q = 1) : d111741 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8460, d111741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8460, d111741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8461 q = 1) (hb : d92315 q = 1) : d111742 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8461, d111742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8461, d111742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8462 q = 1) (hb : d92315 q = 1) : d111743 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8462, d111743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8462, d111743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8496 q = 1) (hb : d92315 q = 1) : d111761 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8496, d111761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8496, d111761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro20552 (p : Pattern) (ha : d8501 p = 1) (hb : d92315 p = 1) : d111867 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8314 q = 1) (hb : d92315 q = 1) : d98846 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8314, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20520 q ha hb
    | true =>
      simp only [d8314, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8315 q = 1) (hb : d92315 q = 1) : d98847 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8315, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8315, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8476 q = 1) (hb : d92315 q = 1) : d111845 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8476, d111845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8476, d111845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8477 q = 1) (hb : d92315 q = 1) : d111846 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8477, d111846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8477, d111846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8478 q = 1) (hb : d92315 q = 1) : d111847 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8478, d111847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8478, d111847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8501 q = 1) (hb : d92315 q = 1) : d111867 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8501, d111867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8501, d111867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro20553 (p : Pattern) (ha : d92315 p = 1) (hb : d94273 p = 1) : d111873 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d514 q = 1) (hb : d92315 q = 1) : d514 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8441 q = 1) (hb : d92315 q = 1) : d111825 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8441, d111825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20542 q ha hb
    | true =>
      simp only [d8441, d111825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8442 q = 1) (hb : d92315 q = 1) : d111826 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8442, d111826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8442, d111826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8443 q = 1) (hb : d92315 q = 1) : d111827 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8443, d111827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8443, d111827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8444 q = 1) (hb : d92315 q = 1) : d111828 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8444, d111828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8444, d111828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d524 q = 1) (hb : d92315 q = 1) : d524 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d8448 q = 1) (hb : d92315 q = 1) : d111832 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8448, d111832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20543 q ha hb
    | true =>
      simp only [d8448, d111832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8449 q = 1) (hb : d92315 q = 1) : d111833 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8449, d111833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8449, d111833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d8450 q = 1) (hb : d92315 q = 1) : d111834 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8450, d111834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d8450, d111834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d8464 q = 1) (hb : d92315 q = 1) : d111843 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8464, d111843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20545 q ha hb
    | true =>
      simp only [d8464, d111843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20540 q ha hb
  have h11 (q : Pattern) (ha : d92315 q = 1) (hb : d94264 q = 1) : d111844 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94264, d111844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d94264, d111844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d8480 q = 1) (hb : d92315 q = 1) : d111849 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8480, d111849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20546 q ha hb
    | true =>
      simp only [d8480, d111849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d8481 q = 1) (hb : d92315 q = 1) : d111850 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8481, d111850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d8481, d111850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d92315 q = 1) (hb : d94265 q = 1) : d111851 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94265, d111851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94265, d111851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d92315 q = 1) (hb : d94266 q = 1) : d111852 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94266, d111852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d94266, d111852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d92315 q = 1) (hb : d94267 q = 1) : d111853 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94267, d111853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d94267, d111853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d610 q = 1) (hb : d92315 q = 1) : d610 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d8487 q = 1) (hb : d92315 q = 1) : d111856 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8487, d111856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20548 q ha hb
    | true =>
      simp only [d8487, d111856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d8488 q = 1) (hb : d92315 q = 1) : d111857 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8488, d111857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8488, d111857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d8489 q = 1) (hb : d92315 q = 1) : d111858 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8489, d111858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d8489, d111858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d8490 q = 1) (hb : d92315 q = 1) : d111859 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8490, d111859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8490, d111859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d616 q = 1) (hb : d92315 q = 1) : d616 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d8492 q = 1) (hb : d92315 q = 1) : d111861 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8492, d111861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20549 q ha hb
    | true =>
      simp only [d8492, d111861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d8493 q = 1) (hb : d92315 q = 1) : d111862 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8493, d111862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8493, d111862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d8494 q = 1) (hb : d92315 q = 1) : d111863 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8494, d111863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d8494, d111863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d8497 q = 1) (hb : d92315 q = 1) : d111865 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8497, d111865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20550 q ha hb
    | true =>
      simp only [d8497, d111865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20551 q ha hb
  have h27 (q : Pattern) (ha : d92315 q = 1) (hb : d94269 q = 1) : d111866 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94269, d111866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q hb ha
    | true =>
      simp only [d94269, d111866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d8502 q = 1) (hb : d92315 q = 1) : d111868 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8502, d111868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20552 q ha hb
    | true =>
      simp only [d8502, d111868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d8503 q = 1) (hb : d92315 q = 1) : d111869 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8503, d111869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d8503, d111869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d92315 q = 1) (hb : d94270 q = 1) : d111870 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94270, d111870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d94270, d111870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q hb ha
  have h31 (q : Pattern) (ha : d92315 q = 1) (hb : d94271 q = 1) : d111871 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94271, d111871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
    | true =>
      simp only [d94271, d111871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d92315 q = 1) (hb : d94272 q = 1) : d111872 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94272, d111872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d94272, d111872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d92315 q = 1) (hb : d94273 q = 1) : d111873 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94273, d111873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d94273, d111873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro20554 (p : Pattern) (ha : d92315 p = 1) (hb : d94280 p = 1) : d111882 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8497 q = 1) (hb : d92315 q = 1) : d111865 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8497, d111865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20550 q ha hb
    | true =>
      simp only [d8497, d111865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20551 q ha hb
  have h2 (q : Pattern) (ha : d92315 q = 1) (hb : d94269 q = 1) : d111866 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94269, d111866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94269, d111866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d8502 q = 1) (hb : d92315 q = 1) : d111868 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8502, d111868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20552 q ha hb
    | true =>
      simp only [d8502, d111868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8503 q = 1) (hb : d92315 q = 1) : d111869 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8503, d111869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8503, d111869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d94270 q = 1) : d111870 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94270, d111870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94270, d111870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d94278 q = 1) : d111880 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94278, d111880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94278, d111880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92315 q = 1) (hb : d94279 q = 1) : d111881 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94279, d111881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94279, d111881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92315 q = 1) (hb : d94280 q = 1) : d111882 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94280, d111882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94280, d111882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20555 (p : Pattern) (ha : d8529 p = 1) (hb : d92315 p = 1) : d111889 p = 1 := by
  have h0 (q : Pattern) (ha : d8527 q = 1) (hb : d92313 q = 1) : d8527 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6843 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8528 q = 1) (hb : d92315 q = 1) : d111888 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8528, d92315, d111888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8528, d92315, d111888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8529 q = 1) (hb : d92315 q = 1) : d111889 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8529, d111889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8529, d111889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro20556 (p : Pattern) (ha : d8535 p = 1) (hb : d92315 p = 1) : d111895 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8530 q = 1) (hb : d92315 q = 1) : d111890 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8530, d111890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20555 q ha hb
    | true =>
      simp only [d8530, d111890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8531 q = 1) (hb : d92315 q = 1) : d111891 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8531, d111891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8531, d111891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6846 q = 1) (hb : d92315 q = 1) : d98879 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6846, d98879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14011 q ha hb
    | true =>
      simp only [d6846, d98879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6847 q = 1) (hb : d92315 q = 1) : d98880 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6847, d98880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6847, d98880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8532 q = 1) (hb : d92315 q = 1) : d111892 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8532, d111892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8532, d111892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8533 q = 1) (hb : d92315 q = 1) : d111893 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8533, d111893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8533, d111893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8534 q = 1) (hb : d92315 q = 1) : d111894 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8534, d111894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8534, d111894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8535 q = 1) (hb : d92315 q = 1) : d111895 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8535, d111895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8535, d111895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro20557 (p : Pattern) (ha : d8539 p = 1) (hb : d92315 p = 1) : d111786 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6846 q = 1) (hb : d92315 q = 1) : d98879 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6846, d98879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14011 q ha hb
    | true =>
      simp only [d6846, d98879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6847 q = 1) (hb : d92315 q = 1) : d98880 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6847, d98880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6847, d98880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d685 q = 1) (hb : d92315 q = 1) : d685 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8536 q = 1) (hb : d92315 q = 1) : d111783 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8536, d111783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8536, d111783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8537 q = 1) (hb : d92315 q = 1) : d111784 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8537, d111784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8537, d111784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8538 q = 1) (hb : d92315 q = 1) : d111785 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8538, d111785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8538, d111785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8539 q = 1) (hb : d92315 q = 1) : d111786 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8539, d111786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8539, d111786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro20558 (p : Pattern) (ha : d8555 p = 1) (hb : d92315 p = 1) : d111901 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8378 q = 1) (hb : d92315 q = 1) : d98879 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8378, d98879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20530 q ha hb
    | true =>
      simp only [d8378, d98879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8379 q = 1) (hb : d92315 q = 1) : d98880 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8379, d98880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8379, d98880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8552 q = 1) (hb : d92315 q = 1) : d111898 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8552, d111898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8552, d111898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8553 q = 1) (hb : d92315 q = 1) : d111899 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8553, d111899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8553, d111899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8554 q = 1) (hb : d92315 q = 1) : d111900 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8554, d111900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8554, d111900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8555 q = 1) (hb : d92315 q = 1) : d111901 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8555, d111901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8555, d111901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro20559 (p : Pattern) (ha : d92315 p = 1) (hb : d94290 p = 1) : d111907 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8540 q = 1) (hb : d92315 q = 1) : d111896 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8540, d111896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20556 q ha hb
    | true =>
      simp only [d8540, d111896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20557 q ha hb
  have h2 (q : Pattern) (ha : d92315 q = 1) (hb : d94286 q = 1) : d111897 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94286, d111897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94286, d111897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d8556 q = 1) (hb : d92315 q = 1) : d111902 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8556, d111902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20558 q ha hb
    | true =>
      simp only [d8556, d111902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8557 q = 1) (hb : d92315 q = 1) : d111903 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8557, d111903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8557, d111903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d94287 q = 1) : d111904 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94287, d111904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94287, d111904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d94288 q = 1) : d111905 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94288, d111905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94288, d111905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92315 q = 1) (hb : d94289 q = 1) : d111906 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94289, d111906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94289, d111906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92315 q = 1) (hb : d94290 q = 1) : d111907 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94290, d111907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94290, d111907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20560 (p : Pattern) (ha : d92315 p = 1) (hb : d94296 p = 1) : d111913 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8427 q = 1) (hb : d92315 q = 1) : d111812 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8427, d111812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8427, d111812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20537 q ha hb
  have h2 (q : Pattern) (ha : d8428 q = 1) (hb : d92315 q = 1) : d111813 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8428, d111813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8428, d111813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8436 q = 1) (hb : d92315 q = 1) : d111820 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8436, d111820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20537 q ha hb
    | true =>
      simp only [d8436, d111820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20539 q ha hb
  have h4 (q : Pattern) (ha : d8437 q = 1) (hb : d92315 q = 1) : d111821 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8437, d111821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8437, d111821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8438 q = 1) (hb : d92315 q = 1) : d111822 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d8438, d111822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8438, d111822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d94274 q = 1) : d111874 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94274, d111874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20547 q ha hb
    | true =>
      simp only [d94274, d111874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20553 q ha hb
  have h7 (q : Pattern) (ha : d644 q = 1) (hb : d92315 q = 1) : d644 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d8515 q = 1) (hb : d92315 q = 1) : d111876 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8515, d111876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20541 q ha hb
    | true =>
      simp only [d8515, d111876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92315 q = 1) (hb : d94275 q = 1) : d111877 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94275, d111877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94275, d111877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d92315 q = 1) (hb : d94276 q = 1) : d111878 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94276, d111878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94276, d111878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d92315 q = 1) (hb : d94277 q = 1) : d111879 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94277, d111879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d94277, d111879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d92315 q = 1) (hb : d94281 q = 1) : d111883 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94281, d111883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94281, d111883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20554 q ha hb
  have h13 (q : Pattern) (ha : d654 q = 1) (hb : d92315 q = 1) : d654 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d92315 q = 1) (hb : d94282 q = 1) : d111884 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94282, d111884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d94282, d111884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d92315 q = 1) (hb : d94283 q = 1) : d111885 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94283, d111885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d94283, d111885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d92315 q = 1) (hb : d94284 q = 1) : d111886 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94284, d111886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d94284, d111886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d92315 q = 1) (hb : d94285 q = 1) : d111887 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94285, d111887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94285, d111887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d92315 q = 1) (hb : d94291 q = 1) : d111908 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94291, d111908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94291, d111908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20559 q ha hb
  have h19 (q : Pattern) (ha : d737 q = 1) (hb : d92315 q = 1) : d737 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d92315 q = 1) (hb : d94292 q = 1) : d111909 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94292, d111909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d94292, d111909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d92315 q = 1) (hb : d94293 q = 1) : d111910 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94293, d111910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d94293, d111910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d92315 q = 1) (hb : d94294 q = 1) : d111911 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94294, d111911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d94294, d111911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d92315 q = 1) (hb : d94295 q = 1) : d111912 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94295, d111912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d94295, d111912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d92315 q = 1) (hb : d94296 q = 1) : d111913 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94296, d111913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d94296, d111913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro20561 (p : Pattern) (ha : d92315 p = 1) (hb : d94302 p = 1) : d111919 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92315 q = 1) (hb : d94297 q = 1) : d111914 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94297, d111914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94297, d111914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20560 q ha hb
  have h2 (q : Pattern) (ha : d92315 q = 1) (hb : d94298 q = 1) : d111915 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94298, d111915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94298, d111915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92315 q = 1) (hb : d94299 q = 1) : d111916 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94299, d111916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94299, d111916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92315 q = 1) (hb : d94300 q = 1) : d111917 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94300, d111917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94300, d111917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d94301 q = 1) : d111918 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94301, d111918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94301, d111918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d94302 q = 1) : d111919 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94302, d111919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94302, d111919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20562 (p : Pattern) (ha : d8576 p = 1) (hb : d92315 p = 1) : d98905 p = 1 := by
  have h0 (q : Pattern) (ha : d6875 q = 1) (hb : d92313 q = 1) : d6875 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d767 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8575 q = 1) (hb : d92315 q = 1) : d98904 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8575, d92315, d98904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8575, d92315, d98904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8576 q = 1) (hb : d92315 q = 1) : d98905 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8576, d98905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8576, d98905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro20563 (p : Pattern) (ha : d8582 p = 1) (hb : d92315 p = 1) : d111924 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8577 q = 1) (hb : d92315 q = 1) : d98906 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8577, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20562 q ha hb
    | true =>
      simp only [d8577, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8578 q = 1) (hb : d92315 q = 1) : d98907 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8578, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8578, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d775 q = 1) (hb : d92315 q = 1) : d775 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8579 q = 1) (hb : d92315 q = 1) : d111921 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8579, d111921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8579, d111921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8580 q = 1) (hb : d92315 q = 1) : d111922 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8580, d111922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8580, d111922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8581 q = 1) (hb : d92315 q = 1) : d111923 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8581, d111923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8581, d111923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8582 q = 1) (hb : d92315 q = 1) : d111924 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8582, d111924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8582, d111924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro20564 (p : Pattern) (ha : d8588 p = 1) (hb : d92315 p = 1) : d111930 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d783 q = 1) (hb : d92315 q = 1) : d783 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8583 q = 1) (hb : d92315 q = 1) : d111925 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8583, d111925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20563 q ha hb
    | true =>
      simp only [d8583, d111925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8584 q = 1) (hb : d92315 q = 1) : d111926 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8584, d111926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8584, d111926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8585 q = 1) (hb : d92315 q = 1) : d111927 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8585, d111927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8585, d111927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8586 q = 1) (hb : d92315 q = 1) : d111928 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8586, d111928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8586, d111928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8587 q = 1) (hb : d92315 q = 1) : d111929 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8587, d111929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8587, d111929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8588 q = 1) (hb : d92315 q = 1) : d111930 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8588, d111930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8588, d111930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro20565 (p : Pattern) (ha : d8591 p = 1) (hb : d92315 p = 1) : d111933 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8577 q = 1) (hb : d92315 q = 1) : d98906 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8577, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20562 q ha hb
    | true =>
      simp only [d8577, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8578 q = 1) (hb : d92315 q = 1) : d98907 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8578, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8578, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d775 q = 1) (hb : d92315 q = 1) : d775 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8579 q = 1) (hb : d92315 q = 1) : d111921 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8579, d111921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8579, d111921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8580 q = 1) (hb : d92315 q = 1) : d111922 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8580, d111922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8580, d111922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8581 q = 1) (hb : d92315 q = 1) : d111923 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8581, d111923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8581, d111923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8591 q = 1) (hb : d92315 q = 1) : d111933 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8591, d111933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8591, d111933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro20566 (p : Pattern) (ha : d8597 p = 1) (hb : d92315 p = 1) : d111939 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d783 q = 1) (hb : d92315 q = 1) : d783 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8583 q = 1) (hb : d92315 q = 1) : d111925 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8583, d111925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20563 q ha hb
    | true =>
      simp only [d8583, d111925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8584 q = 1) (hb : d92315 q = 1) : d111926 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8584, d111926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8584, d111926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8585 q = 1) (hb : d92315 q = 1) : d111927 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8585, d111927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8585, d111927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8586 q = 1) (hb : d92315 q = 1) : d111928 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8586, d111928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8586, d111928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8587 q = 1) (hb : d92315 q = 1) : d111929 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8587, d111929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8587, d111929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d793 q = 1) (hb : d92315 q = 1) : d793 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d8592 q = 1) (hb : d92315 q = 1) : d111934 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8592, d111934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20565 q ha hb
    | true =>
      simp only [d8592, d111934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d8593 q = 1) (hb : d92315 q = 1) : d111935 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8593, d111935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8593, d111935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d8594 q = 1) (hb : d92315 q = 1) : d111936 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8594, d111936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d8594, d111936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d8595 q = 1) (hb : d92315 q = 1) : d111937 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8595, d111937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8595, d111937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d8596 q = 1) (hb : d92315 q = 1) : d111938 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8596, d111938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8596, d111938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d8597 q = 1) (hb : d92315 q = 1) : d111939 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8597, d111939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8597, d111939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro20567 (p : Pattern) (ha : d8625 p = 1) (hb : d92315 p = 1) : d111924 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6878 q = 1) (hb : d92315 q = 1) : d98906 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6878, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14026 q ha hb
    | true =>
      simp only [d6878, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6879 q = 1) (hb : d92315 q = 1) : d98907 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6879, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6879, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d775 q = 1) (hb : d92315 q = 1) : d775 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8622 q = 1) (hb : d92315 q = 1) : d111921 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8622, d111921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8622, d111921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8623 q = 1) (hb : d92315 q = 1) : d111922 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8623, d111922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8623, d111922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8624 q = 1) (hb : d92315 q = 1) : d111923 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8624, d111923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8624, d111923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8625 q = 1) (hb : d92315 q = 1) : d111924 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8625, d111924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8625, d111924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro20568 (p : Pattern) (ha : d8676 p = 1) (hb : d92315 p = 1) : d111995 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d783 q = 1) (hb : d92315 q = 1) : d783 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8671 q = 1) (hb : d92315 q = 1) : d111925 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8671, d111925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20567 q ha hb
    | true =>
      simp only [d8671, d111925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8672 q = 1) (hb : d92315 q = 1) : d111926 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8672, d111926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8672, d111926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8673 q = 1) (hb : d92315 q = 1) : d111927 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8673, d111927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8673, d111927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8674 q = 1) (hb : d92315 q = 1) : d111928 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8674, d111928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8674, d111928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8675 q = 1) (hb : d92315 q = 1) : d111929 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8675, d111929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8675, d111929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d943 q = 1) (hb : d92315 q = 1) : d943 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d8676 q = 1) (hb : d92315 q = 1) : d111995 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8676, d111995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8676, d111995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20569 (p : Pattern) (ha : d8602 p = 1) (hb : d92315 p = 1) : d111944 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8577 q = 1) (hb : d92315 q = 1) : d98906 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8577, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20562 q ha hb
    | true =>
      simp only [d8577, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8578 q = 1) (hb : d92315 q = 1) : d98907 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8578, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8578, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d775 q = 1) (hb : d92315 q = 1) : d775 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8579 q = 1) (hb : d92315 q = 1) : d111921 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8579, d111921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8579, d111921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8580 q = 1) (hb : d92315 q = 1) : d111922 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8580, d111922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8580, d111922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8601 q = 1) (hb : d92315 q = 1) : d111943 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8601, d111943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8601, d111943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8602 q = 1) (hb : d92315 q = 1) : d111944 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8602, d111944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8602, d111944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro20570 (p : Pattern) (ha : d8609 p = 1) (hb : d92315 p = 1) : d111951 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8577 q = 1) (hb : d92315 q = 1) : d98906 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8577, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20562 q ha hb
    | true =>
      simp only [d8577, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8578 q = 1) (hb : d92315 q = 1) : d98907 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8578, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8578, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d775 q = 1) (hb : d92315 q = 1) : d775 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8579 q = 1) (hb : d92315 q = 1) : d111921 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8579, d111921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8579, d111921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8607 q = 1) (hb : d92315 q = 1) : d111949 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8607, d111949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8607, d111949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8608 q = 1) (hb : d92315 q = 1) : d111950 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8608, d111950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8608, d111950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8609 q = 1) (hb : d92315 q = 1) : d111951 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8609, d111951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8609, d111951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro20571 (p : Pattern) (ha : d8615 p = 1) (hb : d92315 p = 1) : d111956 p = 1 := by
  have h0 (q : Pattern) (ha : d8613 q = 1) (hb : d92313 q = 1) : d8613 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6875 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8614 q = 1) (hb : d92315 q = 1) : d111955 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8614, d92315, d111955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8614, d92315, d111955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8615 q = 1) (hb : d92315 q = 1) : d111956 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8615, d111956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8615, d111956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro20572 (p : Pattern) (ha : d8621 p = 1) (hb : d92315 p = 1) : d111962 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8616 q = 1) (hb : d92315 q = 1) : d111957 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8616, d111957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20571 q ha hb
    | true =>
      simp only [d8616, d111957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8617 q = 1) (hb : d92315 q = 1) : d111958 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8617, d111958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8617, d111958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6878 q = 1) (hb : d92315 q = 1) : d98906 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6878, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14026 q ha hb
    | true =>
      simp only [d6878, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6879 q = 1) (hb : d92315 q = 1) : d98907 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6879, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6879, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8618 q = 1) (hb : d92315 q = 1) : d111959 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8618, d111959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8618, d111959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8619 q = 1) (hb : d92315 q = 1) : d111960 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8619, d111960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8619, d111960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8620 q = 1) (hb : d92315 q = 1) : d111961 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8620, d111961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8620, d111961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8621 q = 1) (hb : d92315 q = 1) : d111962 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8621, d111962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8621, d111962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20573 (p : Pattern) (ha : d8641 p = 1) (hb : d92315 p = 1) : d111968 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8577 q = 1) (hb : d92315 q = 1) : d98906 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8577, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20562 q ha hb
    | true =>
      simp only [d8577, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8578 q = 1) (hb : d92315 q = 1) : d98907 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8578, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8578, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8638 q = 1) (hb : d92315 q = 1) : d111965 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8638, d111965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8638, d111965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8639 q = 1) (hb : d92315 q = 1) : d111966 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8639, d111966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8639, d111966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8640 q = 1) (hb : d92315 q = 1) : d111967 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8640, d111967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8640, d111967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8641 q = 1) (hb : d92315 q = 1) : d111968 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8641, d111968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8641, d111968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20574 (p : Pattern) (ha : d92315 p = 1) (hb : d94308 p = 1) : d111974 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d806 q = 1) (hb : d92315 q = 1) : d806 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8603 q = 1) (hb : d92315 q = 1) : d111945 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8603, d111945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20569 q ha hb
    | true =>
      simp only [d8603, d111945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8604 q = 1) (hb : d92315 q = 1) : d111946 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8604, d111946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8604, d111946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8605 q = 1) (hb : d92315 q = 1) : d111947 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8605, d111947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8605, d111947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8606 q = 1) (hb : d92315 q = 1) : d111948 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8606, d111948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8606, d111948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d816 q = 1) (hb : d92315 q = 1) : d816 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d8610 q = 1) (hb : d92315 q = 1) : d111952 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8610, d111952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20570 q ha hb
    | true =>
      simp only [d8610, d111952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8611 q = 1) (hb : d92315 q = 1) : d111953 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8611, d111953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8611, d111953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d8612 q = 1) (hb : d92315 q = 1) : d111954 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8612, d111954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d8612, d111954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d8626 q = 1) (hb : d92315 q = 1) : d111963 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8626, d111963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20572 q ha hb
    | true =>
      simp only [d8626, d111963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20567 q ha hb
  have h11 (q : Pattern) (ha : d92315 q = 1) (hb : d94304 q = 1) : d111964 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94304, d111964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d94304, d111964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d8642 q = 1) (hb : d92315 q = 1) : d111969 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8642, d111969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20573 q ha hb
    | true =>
      simp only [d8642, d111969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d8643 q = 1) (hb : d92315 q = 1) : d111970 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8643, d111970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d8643, d111970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d92315 q = 1) (hb : d94305 q = 1) : d111971 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94305, d111971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94305, d111971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d92315 q = 1) (hb : d94306 q = 1) : d111972 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94306, d111972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d94306, d111972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d92315 q = 1) (hb : d94307 q = 1) : d111973 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94307, d111973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d94307, d111973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d92315 q = 1) (hb : d94308 q = 1) : d111974 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94308, d111974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94308, d111974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro20575 (p : Pattern) (ha : d8648 p = 1) (hb : d92315 p = 1) : d111975 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8577 q = 1) (hb : d92315 q = 1) : d98906 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8577, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20562 q ha hb
    | true =>
      simp only [d8577, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8578 q = 1) (hb : d92315 q = 1) : d98907 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8578, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8578, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d775 q = 1) (hb : d92315 q = 1) : d775 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8579 q = 1) (hb : d92315 q = 1) : d111921 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8579, d111921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8579, d111921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8580 q = 1) (hb : d92315 q = 1) : d111922 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8580, d111922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8580, d111922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8601 q = 1) (hb : d92315 q = 1) : d111943 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8601, d111943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8601, d111943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8648 q = 1) (hb : d92315 q = 1) : d111975 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8648, d111975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8648, d111975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro20576 (p : Pattern) (ha : d8653 p = 1) (hb : d92315 p = 1) : d111980 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8577 q = 1) (hb : d92315 q = 1) : d98906 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8577, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20562 q ha hb
    | true =>
      simp only [d8577, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8578 q = 1) (hb : d92315 q = 1) : d98907 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8578, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8578, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d775 q = 1) (hb : d92315 q = 1) : d775 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8579 q = 1) (hb : d92315 q = 1) : d111921 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8579, d111921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8579, d111921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8607 q = 1) (hb : d92315 q = 1) : d111949 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8607, d111949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8607, d111949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8608 q = 1) (hb : d92315 q = 1) : d111950 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8608, d111950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8608, d111950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8653 q = 1) (hb : d92315 q = 1) : d111980 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8653, d111980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8653, d111980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro20577 (p : Pattern) (ha : d8657 p = 1) (hb : d92315 p = 1) : d111984 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8616 q = 1) (hb : d92315 q = 1) : d111957 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8616, d111957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20571 q ha hb
    | true =>
      simp only [d8616, d111957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8617 q = 1) (hb : d92315 q = 1) : d111958 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8617, d111958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8617, d111958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6878 q = 1) (hb : d92315 q = 1) : d98906 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6878, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14026 q ha hb
    | true =>
      simp only [d6878, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6879 q = 1) (hb : d92315 q = 1) : d98907 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6879, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6879, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8618 q = 1) (hb : d92315 q = 1) : d111959 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8618, d111959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8618, d111959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8619 q = 1) (hb : d92315 q = 1) : d111960 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8619, d111960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8619, d111960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8620 q = 1) (hb : d92315 q = 1) : d111961 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8620, d111961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8620, d111961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8657 q = 1) (hb : d92315 q = 1) : d111984 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8657, d111984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8657, d111984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro20578 (p : Pattern) (ha : d8658 p = 1) (hb : d92315 p = 1) : d111933 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6878 q = 1) (hb : d92315 q = 1) : d98906 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6878, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14026 q ha hb
    | true =>
      simp only [d6878, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6879 q = 1) (hb : d92315 q = 1) : d98907 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6879, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6879, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d775 q = 1) (hb : d92315 q = 1) : d775 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8622 q = 1) (hb : d92315 q = 1) : d111921 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8622, d111921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8622, d111921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8623 q = 1) (hb : d92315 q = 1) : d111922 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8623, d111922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8623, d111922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8624 q = 1) (hb : d92315 q = 1) : d111923 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8624, d111923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8624, d111923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8658 q = 1) (hb : d92315 q = 1) : d111933 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8658, d111933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8658, d111933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro20579 (p : Pattern) (ha : d8663 p = 1) (hb : d92315 p = 1) : d111987 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8577 q = 1) (hb : d92315 q = 1) : d98906 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8577, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20562 q ha hb
    | true =>
      simp only [d8577, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8578 q = 1) (hb : d92315 q = 1) : d98907 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8578, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8578, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8638 q = 1) (hb : d92315 q = 1) : d111965 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8638, d111965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8638, d111965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8639 q = 1) (hb : d92315 q = 1) : d111966 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8639, d111966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8639, d111966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8640 q = 1) (hb : d92315 q = 1) : d111967 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8640, d111967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8640, d111967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8663 q = 1) (hb : d92315 q = 1) : d111987 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8663, d111987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8663, d111987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro20580 (p : Pattern) (ha : d92315 p = 1) (hb : d94313 p = 1) : d111993 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d806 q = 1) (hb : d92315 q = 1) : d806 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8603 q = 1) (hb : d92315 q = 1) : d111945 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8603, d111945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20569 q ha hb
    | true =>
      simp only [d8603, d111945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8604 q = 1) (hb : d92315 q = 1) : d111946 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8604, d111946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8604, d111946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8605 q = 1) (hb : d92315 q = 1) : d111947 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8605, d111947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8605, d111947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8606 q = 1) (hb : d92315 q = 1) : d111948 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8606, d111948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8606, d111948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d816 q = 1) (hb : d92315 q = 1) : d816 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d8610 q = 1) (hb : d92315 q = 1) : d111952 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8610, d111952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20570 q ha hb
    | true =>
      simp only [d8610, d111952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8611 q = 1) (hb : d92315 q = 1) : d111953 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8611, d111953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8611, d111953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d8612 q = 1) (hb : d92315 q = 1) : d111954 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8612, d111954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d8612, d111954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d8626 q = 1) (hb : d92315 q = 1) : d111963 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8626, d111963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20572 q ha hb
    | true =>
      simp only [d8626, d111963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20567 q ha hb
  have h11 (q : Pattern) (ha : d92315 q = 1) (hb : d94304 q = 1) : d111964 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94304, d111964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d94304, d111964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d8642 q = 1) (hb : d92315 q = 1) : d111969 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8642, d111969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20573 q ha hb
    | true =>
      simp only [d8642, d111969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d8643 q = 1) (hb : d92315 q = 1) : d111970 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8643, d111970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d8643, d111970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d92315 q = 1) (hb : d94305 q = 1) : d111971 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94305, d111971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94305, d111971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d92315 q = 1) (hb : d94306 q = 1) : d111972 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94306, d111972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d94306, d111972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d92315 q = 1) (hb : d94307 q = 1) : d111973 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94307, d111973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d94307, d111973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d916 q = 1) (hb : d92315 q = 1) : d916 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d8649 q = 1) (hb : d92315 q = 1) : d111976 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8649, d111976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20575 q ha hb
    | true =>
      simp only [d8649, d111976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d8650 q = 1) (hb : d92315 q = 1) : d111977 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8650, d111977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8650, d111977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d8651 q = 1) (hb : d92315 q = 1) : d111978 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8651, d111978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d8651, d111978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d8652 q = 1) (hb : d92315 q = 1) : d111979 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8652, d111979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8652, d111979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d922 q = 1) (hb : d92315 q = 1) : d922 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d8654 q = 1) (hb : d92315 q = 1) : d111981 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8654, d111981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20576 q ha hb
    | true =>
      simp only [d8654, d111981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d8655 q = 1) (hb : d92315 q = 1) : d111982 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8655, d111982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8655, d111982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d8656 q = 1) (hb : d92315 q = 1) : d111983 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8656, d111983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d8656, d111983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d8659 q = 1) (hb : d92315 q = 1) : d111985 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8659, d111985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20577 q ha hb
    | true =>
      simp only [d8659, d111985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20578 q ha hb
  have h27 (q : Pattern) (ha : d92315 q = 1) (hb : d94309 q = 1) : d111986 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94309, d111986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q hb ha
    | true =>
      simp only [d94309, d111986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d8664 q = 1) (hb : d92315 q = 1) : d111988 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8664, d111988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20579 q ha hb
    | true =>
      simp only [d8664, d111988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d8665 q = 1) (hb : d92315 q = 1) : d111989 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8665, d111989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d8665, d111989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d92315 q = 1) (hb : d94310 q = 1) : d111990 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94310, d111990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d94310, d111990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q hb ha
  have h31 (q : Pattern) (ha : d92315 q = 1) (hb : d94311 q = 1) : d111991 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94311, d111991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
    | true =>
      simp only [d94311, d111991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d92315 q = 1) (hb : d94312 q = 1) : d111992 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94312, d111992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d94312, d111992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d92315 q = 1) (hb : d94313 q = 1) : d111993 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94313, d111993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d94313, d111993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro20581 (p : Pattern) (ha : d92315 p = 1) (hb : d94320 p = 1) : d112002 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8659 q = 1) (hb : d92315 q = 1) : d111985 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8659, d111985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20577 q ha hb
    | true =>
      simp only [d8659, d111985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20578 q ha hb
  have h2 (q : Pattern) (ha : d92315 q = 1) (hb : d94309 q = 1) : d111986 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94309, d111986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94309, d111986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d8664 q = 1) (hb : d92315 q = 1) : d111988 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8664, d111988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20579 q ha hb
    | true =>
      simp only [d8664, d111988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8665 q = 1) (hb : d92315 q = 1) : d111989 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8665, d111989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8665, d111989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d94310 q = 1) : d111990 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94310, d111990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94310, d111990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d94318 q = 1) : d112000 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94318, d112000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94318, d112000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92315 q = 1) (hb : d94319 q = 1) : d112001 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94319, d112001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94319, d112001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92315 q = 1) (hb : d94320 q = 1) : d112002 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94320, d112002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94320, d112002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20582 (p : Pattern) (ha : d8691 p = 1) (hb : d92315 p = 1) : d112009 p = 1 := by
  have h0 (q : Pattern) (ha : d8689 q = 1) (hb : d92313 q = 1) : d8689 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6921 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8690 q = 1) (hb : d92315 q = 1) : d112008 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8690, d92315, d112008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8690, d92315, d112008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8691 q = 1) (hb : d92315 q = 1) : d112009 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8691, d112009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8691, d112009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro20583 (p : Pattern) (ha : d8697 p = 1) (hb : d92315 p = 1) : d112015 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8692 q = 1) (hb : d92315 q = 1) : d112010 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8692, d112010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20582 q ha hb
    | true =>
      simp only [d8692, d112010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8693 q = 1) (hb : d92315 q = 1) : d112011 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8693, d112011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8693, d112011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6924 q = 1) (hb : d92315 q = 1) : d98939 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6924, d98939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14037 q ha hb
    | true =>
      simp only [d6924, d98939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6925 q = 1) (hb : d92315 q = 1) : d98940 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6925, d98940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6925, d98940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8694 q = 1) (hb : d92315 q = 1) : d112012 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8694, d112012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8694, d112012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8695 q = 1) (hb : d92315 q = 1) : d112013 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8695, d112013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8695, d112013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8696 q = 1) (hb : d92315 q = 1) : d112014 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8696, d112014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8696, d112014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8697 q = 1) (hb : d92315 q = 1) : d112015 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8697, d112015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8697, d112015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro20584 (p : Pattern) (ha : d8701 p = 1) (hb : d92315 p = 1) : d112019 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6924 q = 1) (hb : d92315 q = 1) : d98939 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6924, d98939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14037 q ha hb
    | true =>
      simp only [d6924, d98939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6925 q = 1) (hb : d92315 q = 1) : d98940 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6925, d98940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6925, d98940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1007 q = 1) (hb : d92315 q = 1) : d1007 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8698 q = 1) (hb : d92315 q = 1) : d112016 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8698, d112016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8698, d112016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8699 q = 1) (hb : d92315 q = 1) : d112017 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8699, d112017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8699, d112017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8700 q = 1) (hb : d92315 q = 1) : d112018 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8700, d112018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8700, d112018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8701 q = 1) (hb : d92315 q = 1) : d112019 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8701, d112019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8701, d112019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro20585 (p : Pattern) (ha : d8715 p = 1) (hb : d92315 p = 1) : d98938 p = 1 := by
  have h0 (q : Pattern) (ha : d6921 q = 1) (hb : d92313 q = 1) : d6921 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d995 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8714 q = 1) (hb : d92315 q = 1) : d98937 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8714, d92315, d98937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8714, d92315, d98937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8715 q = 1) (hb : d92315 q = 1) : d98938 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8715, d98938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8715, d98938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro20586 (p : Pattern) (ha : d8721 p = 1) (hb : d92315 p = 1) : d112025 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8716 q = 1) (hb : d92315 q = 1) : d98939 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8716, d98939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20585 q ha hb
    | true =>
      simp only [d8716, d98939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8717 q = 1) (hb : d92315 q = 1) : d98940 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8717, d98940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8717, d98940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8718 q = 1) (hb : d92315 q = 1) : d112022 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8718, d112022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8718, d112022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8719 q = 1) (hb : d92315 q = 1) : d112023 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8719, d112023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8719, d112023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8720 q = 1) (hb : d92315 q = 1) : d112024 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8720, d112024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8720, d112024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8721 q = 1) (hb : d92315 q = 1) : d112025 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8721, d112025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8721, d112025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro20587 (p : Pattern) (ha : d92315 p = 1) (hb : d94330 p = 1) : d112031 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8702 q = 1) (hb : d92315 q = 1) : d112020 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8702, d112020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20583 q ha hb
    | true =>
      simp only [d8702, d112020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20584 q ha hb
  have h2 (q : Pattern) (ha : d92315 q = 1) (hb : d94326 q = 1) : d112021 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94326, d112021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94326, d112021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d8722 q = 1) (hb : d92315 q = 1) : d112026 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8722, d112026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20586 q ha hb
    | true =>
      simp only [d8722, d112026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8723 q = 1) (hb : d92315 q = 1) : d112027 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8723, d112027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8723, d112027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d94327 q = 1) : d112028 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94327, d112028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94327, d112028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d94328 q = 1) : d112029 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94328, d112029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94328, d112029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92315 q = 1) (hb : d94329 q = 1) : d112030 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94329, d112030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94329, d112030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92315 q = 1) (hb : d94330 q = 1) : d112031 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94330, d112031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94330, d112031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20588 (p : Pattern) (ha : d92315 p = 1) (hb : d94336 p = 1) : d112037 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8589 q = 1) (hb : d92315 q = 1) : d111931 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8589, d111931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8589, d111931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20564 q ha hb
  have h2 (q : Pattern) (ha : d8590 q = 1) (hb : d92315 q = 1) : d111932 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8590, d111932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8590, d111932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8598 q = 1) (hb : d92315 q = 1) : d111940 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8598, d111940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20564 q ha hb
    | true =>
      simp only [d8598, d111940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20566 q ha hb
  have h4 (q : Pattern) (ha : d8599 q = 1) (hb : d92315 q = 1) : d111941 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8599, d111941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8599, d111941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8600 q = 1) (hb : d92315 q = 1) : d111942 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d8600, d111942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8600, d111942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d94314 q = 1) : d111994 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94314, d111994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20574 q ha hb
    | true =>
      simp only [d94314, d111994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20580 q ha hb
  have h7 (q : Pattern) (ha : d950 q = 1) (hb : d92315 q = 1) : d950 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d8677 q = 1) (hb : d92315 q = 1) : d111996 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8677, d111996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20568 q ha hb
    | true =>
      simp only [d8677, d111996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92315 q = 1) (hb : d94315 q = 1) : d111997 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94315, d111997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94315, d111997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d92315 q = 1) (hb : d94316 q = 1) : d111998 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94316, d111998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94316, d111998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d92315 q = 1) (hb : d94317 q = 1) : d111999 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94317, d111999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d94317, d111999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d92315 q = 1) (hb : d94321 q = 1) : d112003 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94321, d112003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94321, d112003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20581 q ha hb
  have h13 (q : Pattern) (ha : d960 q = 1) (hb : d92315 q = 1) : d960 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d92315 q = 1) (hb : d94322 q = 1) : d112004 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94322, d112004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d94322, d112004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d92315 q = 1) (hb : d94323 q = 1) : d112005 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94323, d112005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d94323, d112005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d92315 q = 1) (hb : d94324 q = 1) : d112006 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94324, d112006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d94324, d112006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d92315 q = 1) (hb : d94325 q = 1) : d112007 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94325, d112007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94325, d112007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d92315 q = 1) (hb : d94331 q = 1) : d112032 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94331, d112032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94331, d112032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20587 q ha hb
  have h19 (q : Pattern) (ha : d1070 q = 1) (hb : d92315 q = 1) : d1070 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d92315 q = 1) (hb : d94332 q = 1) : d112033 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94332, d112033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d94332, d112033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d92315 q = 1) (hb : d94333 q = 1) : d112034 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94333, d112034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d94333, d112034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d92315 q = 1) (hb : d94334 q = 1) : d112035 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94334, d112035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d94334, d112035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d92315 q = 1) (hb : d94335 q = 1) : d112036 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94335, d112036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d94335, d112036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d92315 q = 1) (hb : d94336 q = 1) : d112037 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94336, d112037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d94336, d112037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro20589 (p : Pattern) (ha : d92315 p = 1) (hb : d94342 p = 1) : d112043 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92315 q = 1) (hb : d94337 q = 1) : d112038 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94337, d112038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94337, d112038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20588 q ha hb
  have h2 (q : Pattern) (ha : d92315 q = 1) (hb : d94338 q = 1) : d112039 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94338, d112039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94338, d112039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92315 q = 1) (hb : d94339 q = 1) : d112040 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94339, d112040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94339, d112040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92315 q = 1) (hb : d94340 q = 1) : d112041 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94340, d112041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94340, d112041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d94341 q = 1) : d112042 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94341, d112042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94341, d112042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d94342 q = 1) : d112043 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94342, d112043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94342, d112043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20590 (p : Pattern) (ha : d8743 p = 1) (hb : d92315 p = 1) : d98966 p = 1 := by
  have h0 (q : Pattern) (ha : d6954 q = 1) (hb : d92313 q = 1) : d6954 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1146 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8742 q = 1) (hb : d92315 q = 1) : d98965 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8742, d92315, d98965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8742, d92315, d98965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8743 q = 1) (hb : d92315 q = 1) : d98966 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8743, d98966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8743, d98966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro20591 (p : Pattern) (ha : d8749 p = 1) (hb : d92315 p = 1) : d112049 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8744 q = 1) (hb : d92315 q = 1) : d98967 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8744, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20590 q ha hb
    | true =>
      simp only [d8744, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8745 q = 1) (hb : d92315 q = 1) : d98968 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8745, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8745, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1154 q = 1) (hb : d92315 q = 1) : d1154 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8746 q = 1) (hb : d92315 q = 1) : d112046 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8746, d112046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8746, d112046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8747 q = 1) (hb : d92315 q = 1) : d112047 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8747, d112047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8747, d112047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8748 q = 1) (hb : d92315 q = 1) : d112048 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8748, d112048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8748, d112048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8749 q = 1) (hb : d92315 q = 1) : d112049 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8749, d112049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8749, d112049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro20592 (p : Pattern) (ha : d8755 p = 1) (hb : d92315 p = 1) : d112055 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1162 q = 1) (hb : d92315 q = 1) : d1162 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8750 q = 1) (hb : d92315 q = 1) : d112050 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8750, d112050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20591 q ha hb
    | true =>
      simp only [d8750, d112050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8751 q = 1) (hb : d92315 q = 1) : d112051 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8751, d112051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8751, d112051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8752 q = 1) (hb : d92315 q = 1) : d112052 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8752, d112052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8752, d112052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8753 q = 1) (hb : d92315 q = 1) : d112053 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8753, d112053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8753, d112053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8754 q = 1) (hb : d92315 q = 1) : d112054 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8754, d112054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8754, d112054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8755 q = 1) (hb : d92315 q = 1) : d112055 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8755, d112055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8755, d112055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro20593 (p : Pattern) (ha : d8758 p = 1) (hb : d92315 p = 1) : d112058 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8744 q = 1) (hb : d92315 q = 1) : d98967 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8744, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20590 q ha hb
    | true =>
      simp only [d8744, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8745 q = 1) (hb : d92315 q = 1) : d98968 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8745, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8745, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1154 q = 1) (hb : d92315 q = 1) : d1154 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8746 q = 1) (hb : d92315 q = 1) : d112046 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8746, d112046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8746, d112046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8747 q = 1) (hb : d92315 q = 1) : d112047 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8747, d112047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8747, d112047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8748 q = 1) (hb : d92315 q = 1) : d112048 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8748, d112048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8748, d112048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8758 q = 1) (hb : d92315 q = 1) : d112058 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8758, d112058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8758, d112058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro20594 (p : Pattern) (ha : d8764 p = 1) (hb : d92315 p = 1) : d112064 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1162 q = 1) (hb : d92315 q = 1) : d1162 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8750 q = 1) (hb : d92315 q = 1) : d112050 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8750, d112050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20591 q ha hb
    | true =>
      simp only [d8750, d112050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8751 q = 1) (hb : d92315 q = 1) : d112051 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8751, d112051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8751, d112051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8752 q = 1) (hb : d92315 q = 1) : d112052 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8752, d112052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8752, d112052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8753 q = 1) (hb : d92315 q = 1) : d112053 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8753, d112053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8753, d112053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8754 q = 1) (hb : d92315 q = 1) : d112054 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8754, d112054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8754, d112054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1172 q = 1) (hb : d92315 q = 1) : d1172 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d8759 q = 1) (hb : d92315 q = 1) : d112059 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8759, d112059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20593 q ha hb
    | true =>
      simp only [d8759, d112059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d8760 q = 1) (hb : d92315 q = 1) : d112060 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8760, d112060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8760, d112060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d8761 q = 1) (hb : d92315 q = 1) : d112061 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8761, d112061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d8761, d112061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d8762 q = 1) (hb : d92315 q = 1) : d112062 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8762, d112062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8762, d112062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d8763 q = 1) (hb : d92315 q = 1) : d112063 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8763, d112063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8763, d112063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d8764 q = 1) (hb : d92315 q = 1) : d112064 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8764, d112064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8764, d112064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro20595 (p : Pattern) (ha : d8792 p = 1) (hb : d92315 p = 1) : d112049 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6957 q = 1) (hb : d92315 q = 1) : d98967 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6957, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14052 q ha hb
    | true =>
      simp only [d6957, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6958 q = 1) (hb : d92315 q = 1) : d98968 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6958, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6958, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1154 q = 1) (hb : d92315 q = 1) : d1154 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8789 q = 1) (hb : d92315 q = 1) : d112046 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8789, d112046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8789, d112046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8790 q = 1) (hb : d92315 q = 1) : d112047 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8790, d112047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8790, d112047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8791 q = 1) (hb : d92315 q = 1) : d112048 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8791, d112048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8791, d112048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8792 q = 1) (hb : d92315 q = 1) : d112049 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8792, d112049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8792, d112049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro20596 (p : Pattern) (ha : d8843 p = 1) (hb : d92315 p = 1) : d112120 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1162 q = 1) (hb : d92315 q = 1) : d1162 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8838 q = 1) (hb : d92315 q = 1) : d112050 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8838, d112050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20595 q ha hb
    | true =>
      simp only [d8838, d112050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8839 q = 1) (hb : d92315 q = 1) : d112051 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8839, d112051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8839, d112051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8840 q = 1) (hb : d92315 q = 1) : d112052 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8840, d112052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8840, d112052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8841 q = 1) (hb : d92315 q = 1) : d112053 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8841, d112053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8841, d112053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8842 q = 1) (hb : d92315 q = 1) : d112054 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8842, d112054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8842, d112054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1354 q = 1) (hb : d92315 q = 1) : d1354 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d8843 q = 1) (hb : d92315 q = 1) : d112120 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8843, d112120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8843, d112120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20597 (p : Pattern) (ha : d8769 p = 1) (hb : d92315 p = 1) : d112069 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8744 q = 1) (hb : d92315 q = 1) : d98967 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8744, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20590 q ha hb
    | true =>
      simp only [d8744, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8745 q = 1) (hb : d92315 q = 1) : d98968 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8745, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8745, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1154 q = 1) (hb : d92315 q = 1) : d1154 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8746 q = 1) (hb : d92315 q = 1) : d112046 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8746, d112046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8746, d112046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8747 q = 1) (hb : d92315 q = 1) : d112047 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8747, d112047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8747, d112047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8768 q = 1) (hb : d92315 q = 1) : d112068 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8768, d112068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8768, d112068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8769 q = 1) (hb : d92315 q = 1) : d112069 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8769, d112069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8769, d112069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro20598 (p : Pattern) (ha : d8776 p = 1) (hb : d92315 p = 1) : d112076 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8744 q = 1) (hb : d92315 q = 1) : d98967 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8744, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20590 q ha hb
    | true =>
      simp only [d8744, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8745 q = 1) (hb : d92315 q = 1) : d98968 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8745, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8745, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1154 q = 1) (hb : d92315 q = 1) : d1154 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8746 q = 1) (hb : d92315 q = 1) : d112046 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8746, d112046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8746, d112046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8774 q = 1) (hb : d92315 q = 1) : d112074 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8774, d112074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8774, d112074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8775 q = 1) (hb : d92315 q = 1) : d112075 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8775, d112075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8775, d112075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8776 q = 1) (hb : d92315 q = 1) : d112076 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8776, d112076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8776, d112076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro20599 (p : Pattern) (ha : d8782 p = 1) (hb : d92315 p = 1) : d112081 p = 1 := by
  have h0 (q : Pattern) (ha : d8780 q = 1) (hb : d92313 q = 1) : d8780 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6954 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8781 q = 1) (hb : d92315 q = 1) : d112080 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8781, d92315, d112080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8781, d92315, d112080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8782 q = 1) (hb : d92315 q = 1) : d112081 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8782, d112081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8782, d112081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro20600 (p : Pattern) (ha : d8788 p = 1) (hb : d92315 p = 1) : d112087 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8783 q = 1) (hb : d92315 q = 1) : d112082 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8783, d112082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20599 q ha hb
    | true =>
      simp only [d8783, d112082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8784 q = 1) (hb : d92315 q = 1) : d112083 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8784, d112083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8784, d112083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6957 q = 1) (hb : d92315 q = 1) : d98967 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6957, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14052 q ha hb
    | true =>
      simp only [d6957, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6958 q = 1) (hb : d92315 q = 1) : d98968 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6958, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6958, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8785 q = 1) (hb : d92315 q = 1) : d112084 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8785, d112084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8785, d112084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8786 q = 1) (hb : d92315 q = 1) : d112085 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8786, d112085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8786, d112085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8787 q = 1) (hb : d92315 q = 1) : d112086 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8787, d112086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8787, d112086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8788 q = 1) (hb : d92315 q = 1) : d112087 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8788, d112087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8788, d112087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20601 (p : Pattern) (ha : d8808 p = 1) (hb : d92315 p = 1) : d112093 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8744 q = 1) (hb : d92315 q = 1) : d98967 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8744, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20590 q ha hb
    | true =>
      simp only [d8744, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8745 q = 1) (hb : d92315 q = 1) : d98968 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8745, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8745, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8805 q = 1) (hb : d92315 q = 1) : d112090 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8805, d112090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8805, d112090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8806 q = 1) (hb : d92315 q = 1) : d112091 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8806, d112091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8806, d112091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8807 q = 1) (hb : d92315 q = 1) : d112092 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8807, d112092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8807, d112092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8808 q = 1) (hb : d92315 q = 1) : d112093 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8808, d112093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8808, d112093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20602 (p : Pattern) (ha : d92315 p = 1) (hb : d94349 p = 1) : d112099 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1185 q = 1) (hb : d92315 q = 1) : d1185 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8770 q = 1) (hb : d92315 q = 1) : d112070 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8770, d112070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20597 q ha hb
    | true =>
      simp only [d8770, d112070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8771 q = 1) (hb : d92315 q = 1) : d112071 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8771, d112071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8771, d112071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8772 q = 1) (hb : d92315 q = 1) : d112072 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8772, d112072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8772, d112072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8773 q = 1) (hb : d92315 q = 1) : d112073 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8773, d112073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8773, d112073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1195 q = 1) (hb : d92315 q = 1) : d1195 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d8777 q = 1) (hb : d92315 q = 1) : d112077 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8777, d112077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20598 q ha hb
    | true =>
      simp only [d8777, d112077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8778 q = 1) (hb : d92315 q = 1) : d112078 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8778, d112078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8778, d112078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d8779 q = 1) (hb : d92315 q = 1) : d112079 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8779, d112079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d8779, d112079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d8793 q = 1) (hb : d92315 q = 1) : d112088 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8793, d112088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20600 q ha hb
    | true =>
      simp only [d8793, d112088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20595 q ha hb
  have h11 (q : Pattern) (ha : d92315 q = 1) (hb : d94345 q = 1) : d112089 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94345, d112089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d94345, d112089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d8809 q = 1) (hb : d92315 q = 1) : d112094 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8809, d112094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20601 q ha hb
    | true =>
      simp only [d8809, d112094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d8810 q = 1) (hb : d92315 q = 1) : d112095 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8810, d112095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d8810, d112095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d92315 q = 1) (hb : d94346 q = 1) : d112096 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94346, d112096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94346, d112096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d92315 q = 1) (hb : d94347 q = 1) : d112097 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94347, d112097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d94347, d112097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d92315 q = 1) (hb : d94348 q = 1) : d112098 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94348, d112098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d94348, d112098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d92315 q = 1) (hb : d94349 q = 1) : d112099 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94349, d112099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94349, d112099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro20603 (p : Pattern) (ha : d8815 p = 1) (hb : d92315 p = 1) : d112100 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8744 q = 1) (hb : d92315 q = 1) : d98967 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8744, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20590 q ha hb
    | true =>
      simp only [d8744, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8745 q = 1) (hb : d92315 q = 1) : d98968 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8745, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8745, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1154 q = 1) (hb : d92315 q = 1) : d1154 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8746 q = 1) (hb : d92315 q = 1) : d112046 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8746, d112046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8746, d112046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8747 q = 1) (hb : d92315 q = 1) : d112047 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8747, d112047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8747, d112047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8768 q = 1) (hb : d92315 q = 1) : d112068 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8768, d112068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8768, d112068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8815 q = 1) (hb : d92315 q = 1) : d112100 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8815, d112100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8815, d112100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro20604 (p : Pattern) (ha : d8820 p = 1) (hb : d92315 p = 1) : d112105 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8744 q = 1) (hb : d92315 q = 1) : d98967 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8744, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20590 q ha hb
    | true =>
      simp only [d8744, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8745 q = 1) (hb : d92315 q = 1) : d98968 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8745, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8745, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1154 q = 1) (hb : d92315 q = 1) : d1154 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8746 q = 1) (hb : d92315 q = 1) : d112046 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8746, d112046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8746, d112046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8774 q = 1) (hb : d92315 q = 1) : d112074 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8774, d112074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8774, d112074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8775 q = 1) (hb : d92315 q = 1) : d112075 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8775, d112075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8775, d112075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8820 q = 1) (hb : d92315 q = 1) : d112105 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8820, d112105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8820, d112105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro20605 (p : Pattern) (ha : d8824 p = 1) (hb : d92315 p = 1) : d112109 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8783 q = 1) (hb : d92315 q = 1) : d112082 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8783, d112082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20599 q ha hb
    | true =>
      simp only [d8783, d112082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8784 q = 1) (hb : d92315 q = 1) : d112083 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8784, d112083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8784, d112083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6957 q = 1) (hb : d92315 q = 1) : d98967 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6957, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14052 q ha hb
    | true =>
      simp only [d6957, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6958 q = 1) (hb : d92315 q = 1) : d98968 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6958, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6958, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8785 q = 1) (hb : d92315 q = 1) : d112084 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8785, d112084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8785, d112084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8786 q = 1) (hb : d92315 q = 1) : d112085 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8786, d112085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8786, d112085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8787 q = 1) (hb : d92315 q = 1) : d112086 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8787, d112086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8787, d112086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8824 q = 1) (hb : d92315 q = 1) : d112109 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8824, d112109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8824, d112109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro20606 (p : Pattern) (ha : d8825 p = 1) (hb : d92315 p = 1) : d112058 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6957 q = 1) (hb : d92315 q = 1) : d98967 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6957, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14052 q ha hb
    | true =>
      simp only [d6957, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6958 q = 1) (hb : d92315 q = 1) : d98968 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6958, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6958, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1154 q = 1) (hb : d92315 q = 1) : d1154 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8789 q = 1) (hb : d92315 q = 1) : d112046 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8789, d112046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8789, d112046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8790 q = 1) (hb : d92315 q = 1) : d112047 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8790, d112047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8790, d112047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8791 q = 1) (hb : d92315 q = 1) : d112048 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8791, d112048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8791, d112048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8825 q = 1) (hb : d92315 q = 1) : d112058 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8825, d112058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8825, d112058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro20607 (p : Pattern) (ha : d8830 p = 1) (hb : d92315 p = 1) : d112112 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8744 q = 1) (hb : d92315 q = 1) : d98967 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8744, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20590 q ha hb
    | true =>
      simp only [d8744, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8745 q = 1) (hb : d92315 q = 1) : d98968 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8745, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8745, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8805 q = 1) (hb : d92315 q = 1) : d112090 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8805, d112090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8805, d112090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8806 q = 1) (hb : d92315 q = 1) : d112091 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8806, d112091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8806, d112091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8807 q = 1) (hb : d92315 q = 1) : d112092 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8807, d112092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8807, d112092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8830 q = 1) (hb : d92315 q = 1) : d112112 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8830, d112112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8830, d112112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro20608 (p : Pattern) (ha : d92315 p = 1) (hb : d94354 p = 1) : d112118 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1185 q = 1) (hb : d92315 q = 1) : d1185 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8770 q = 1) (hb : d92315 q = 1) : d112070 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8770, d112070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20597 q ha hb
    | true =>
      simp only [d8770, d112070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8771 q = 1) (hb : d92315 q = 1) : d112071 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8771, d112071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8771, d112071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8772 q = 1) (hb : d92315 q = 1) : d112072 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8772, d112072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8772, d112072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8773 q = 1) (hb : d92315 q = 1) : d112073 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8773, d112073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8773, d112073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1195 q = 1) (hb : d92315 q = 1) : d1195 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d8777 q = 1) (hb : d92315 q = 1) : d112077 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8777, d112077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20598 q ha hb
    | true =>
      simp only [d8777, d112077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8778 q = 1) (hb : d92315 q = 1) : d112078 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8778, d112078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8778, d112078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d8779 q = 1) (hb : d92315 q = 1) : d112079 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8779, d112079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d8779, d112079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d8793 q = 1) (hb : d92315 q = 1) : d112088 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8793, d112088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20600 q ha hb
    | true =>
      simp only [d8793, d112088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20595 q ha hb
  have h11 (q : Pattern) (ha : d92315 q = 1) (hb : d94345 q = 1) : d112089 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94345, d112089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d94345, d112089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d8809 q = 1) (hb : d92315 q = 1) : d112094 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8809, d112094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20601 q ha hb
    | true =>
      simp only [d8809, d112094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d8810 q = 1) (hb : d92315 q = 1) : d112095 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8810, d112095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d8810, d112095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d92315 q = 1) (hb : d94346 q = 1) : d112096 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94346, d112096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94346, d112096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d92315 q = 1) (hb : d94347 q = 1) : d112097 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94347, d112097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d94347, d112097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d92315 q = 1) (hb : d94348 q = 1) : d112098 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94348, d112098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d94348, d112098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d1327 q = 1) (hb : d92315 q = 1) : d1327 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d8816 q = 1) (hb : d92315 q = 1) : d112101 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8816, d112101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20603 q ha hb
    | true =>
      simp only [d8816, d112101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d8817 q = 1) (hb : d92315 q = 1) : d112102 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8817, d112102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8817, d112102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d8818 q = 1) (hb : d92315 q = 1) : d112103 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8818, d112103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d8818, d112103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d8819 q = 1) (hb : d92315 q = 1) : d112104 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8819, d112104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8819, d112104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d1333 q = 1) (hb : d92315 q = 1) : d1333 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d8821 q = 1) (hb : d92315 q = 1) : d112106 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8821, d112106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20604 q ha hb
    | true =>
      simp only [d8821, d112106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d8822 q = 1) (hb : d92315 q = 1) : d112107 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8822, d112107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8822, d112107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d8823 q = 1) (hb : d92315 q = 1) : d112108 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8823, d112108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d8823, d112108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d8826 q = 1) (hb : d92315 q = 1) : d112110 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8826, d112110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20605 q ha hb
    | true =>
      simp only [d8826, d112110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20606 q ha hb
  have h27 (q : Pattern) (ha : d92315 q = 1) (hb : d94350 q = 1) : d112111 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94350, d112111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q hb ha
    | true =>
      simp only [d94350, d112111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d8831 q = 1) (hb : d92315 q = 1) : d112113 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8831, d112113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20607 q ha hb
    | true =>
      simp only [d8831, d112113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d8832 q = 1) (hb : d92315 q = 1) : d112114 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8832, d112114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d8832, d112114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d92315 q = 1) (hb : d94351 q = 1) : d112115 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94351, d112115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d94351, d112115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q hb ha
  have h31 (q : Pattern) (ha : d92315 q = 1) (hb : d94352 q = 1) : d112116 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94352, d112116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
    | true =>
      simp only [d94352, d112116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d92315 q = 1) (hb : d94353 q = 1) : d112117 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94353, d112117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d94353, d112117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d92315 q = 1) (hb : d94354 q = 1) : d112118 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94354, d112118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d94354, d112118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro20609 (p : Pattern) (ha : d92315 p = 1) (hb : d94361 p = 1) : d112127 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8826 q = 1) (hb : d92315 q = 1) : d112110 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8826, d112110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20605 q ha hb
    | true =>
      simp only [d8826, d112110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20606 q ha hb
  have h2 (q : Pattern) (ha : d92315 q = 1) (hb : d94350 q = 1) : d112111 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94350, d112111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94350, d112111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d8831 q = 1) (hb : d92315 q = 1) : d112113 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8831, d112113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20607 q ha hb
    | true =>
      simp only [d8831, d112113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8832 q = 1) (hb : d92315 q = 1) : d112114 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8832, d112114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8832, d112114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d94351 q = 1) : d112115 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94351, d112115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94351, d112115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d94359 q = 1) : d112125 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94359, d112125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94359, d112125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92315 q = 1) (hb : d94360 q = 1) : d112126 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94360, d112126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94360, d112126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92315 q = 1) (hb : d94361 q = 1) : d112127 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94361, d112127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94361, d112127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20610 (p : Pattern) (ha : d8858 p = 1) (hb : d92315 p = 1) : d112134 p = 1 := by
  have h0 (q : Pattern) (ha : d8856 q = 1) (hb : d92313 q = 1) : d8856 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7000 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8857 q = 1) (hb : d92315 q = 1) : d112133 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8857, d92315, d112133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8857, d92315, d112133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8858 q = 1) (hb : d92315 q = 1) : d112134 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8858, d112134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8858, d112134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro20611 (p : Pattern) (ha : d8864 p = 1) (hb : d92315 p = 1) : d112140 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8859 q = 1) (hb : d92315 q = 1) : d112135 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8859, d112135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20610 q ha hb
    | true =>
      simp only [d8859, d112135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8860 q = 1) (hb : d92315 q = 1) : d112136 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8860, d112136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8860, d112136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7003 q = 1) (hb : d92315 q = 1) : d99000 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7003, d99000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14063 q ha hb
    | true =>
      simp only [d7003, d99000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7004 q = 1) (hb : d92315 q = 1) : d99001 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7004, d99001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7004, d99001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8861 q = 1) (hb : d92315 q = 1) : d112137 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8861, d112137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8861, d112137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8862 q = 1) (hb : d92315 q = 1) : d112138 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8862, d112138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8862, d112138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8863 q = 1) (hb : d92315 q = 1) : d112139 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8863, d112139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8863, d112139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8864 q = 1) (hb : d92315 q = 1) : d112140 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8864, d112140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8864, d112140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro20612 (p : Pattern) (ha : d8868 p = 1) (hb : d92315 p = 1) : d112144 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7003 q = 1) (hb : d92315 q = 1) : d99000 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7003, d99000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14063 q ha hb
    | true =>
      simp only [d7003, d99000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7004 q = 1) (hb : d92315 q = 1) : d99001 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7004, d99001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7004, d99001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1432 q = 1) (hb : d92315 q = 1) : d1432 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8865 q = 1) (hb : d92315 q = 1) : d112141 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8865, d112141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8865, d112141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8866 q = 1) (hb : d92315 q = 1) : d112142 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8866, d112142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8866, d112142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8867 q = 1) (hb : d92315 q = 1) : d112143 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8867, d112143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8867, d112143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8868 q = 1) (hb : d92315 q = 1) : d112144 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8868, d112144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8868, d112144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro20613 (p : Pattern) (ha : d8882 p = 1) (hb : d92315 p = 1) : d98999 p = 1 := by
  have h0 (q : Pattern) (ha : d7000 q = 1) (hb : d92313 q = 1) : d7000 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1420 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8881 q = 1) (hb : d92315 q = 1) : d98998 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8881, d92315, d98998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8881, d92315, d98998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8882 q = 1) (hb : d92315 q = 1) : d98999 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8882, d98999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8882, d98999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro20614 (p : Pattern) (ha : d8888 p = 1) (hb : d92315 p = 1) : d112150 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8883 q = 1) (hb : d92315 q = 1) : d99000 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8883, d99000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20613 q ha hb
    | true =>
      simp only [d8883, d99000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8884 q = 1) (hb : d92315 q = 1) : d99001 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8884, d99001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8884, d99001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8885 q = 1) (hb : d92315 q = 1) : d112147 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8885, d112147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8885, d112147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8886 q = 1) (hb : d92315 q = 1) : d112148 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8886, d112148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8886, d112148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8887 q = 1) (hb : d92315 q = 1) : d112149 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8887, d112149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8887, d112149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8888 q = 1) (hb : d92315 q = 1) : d112150 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8888, d112150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8888, d112150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro20615 (p : Pattern) (ha : d92315 p = 1) (hb : d94371 p = 1) : d112156 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8869 q = 1) (hb : d92315 q = 1) : d112145 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8869, d112145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20611 q ha hb
    | true =>
      simp only [d8869, d112145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20612 q ha hb
  have h2 (q : Pattern) (ha : d92315 q = 1) (hb : d94367 q = 1) : d112146 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94367, d112146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94367, d112146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d8889 q = 1) (hb : d92315 q = 1) : d112151 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8889, d112151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20614 q ha hb
    | true =>
      simp only [d8889, d112151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8890 q = 1) (hb : d92315 q = 1) : d112152 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8890, d112152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8890, d112152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d94368 q = 1) : d112153 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94368, d112153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94368, d112153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d94369 q = 1) : d112154 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94369, d112154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94369, d112154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92315 q = 1) (hb : d94370 q = 1) : d112155 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94370, d112155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94370, d112155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92315 q = 1) (hb : d94371 q = 1) : d112156 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94371, d112156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94371, d112156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20616 (p : Pattern) (ha : d92315 p = 1) (hb : d94377 p = 1) : d112162 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8756 q = 1) (hb : d92315 q = 1) : d112056 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8756, d112056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8756, d112056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20592 q ha hb
  have h2 (q : Pattern) (ha : d8757 q = 1) (hb : d92315 q = 1) : d112057 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8757, d112057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8757, d112057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8765 q = 1) (hb : d92315 q = 1) : d112065 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8765, d112065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20592 q ha hb
    | true =>
      simp only [d8765, d112065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20594 q ha hb
  have h4 (q : Pattern) (ha : d8766 q = 1) (hb : d92315 q = 1) : d112066 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8766, d112066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8766, d112066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8767 q = 1) (hb : d92315 q = 1) : d112067 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d8767, d112067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8767, d112067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d94355 q = 1) : d112119 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94355, d112119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20602 q ha hb
    | true =>
      simp only [d94355, d112119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20608 q ha hb
  have h7 (q : Pattern) (ha : d1361 q = 1) (hb : d92315 q = 1) : d1361 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d8844 q = 1) (hb : d92315 q = 1) : d112121 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8844, d112121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20596 q ha hb
    | true =>
      simp only [d8844, d112121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92315 q = 1) (hb : d94356 q = 1) : d112122 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94356, d112122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94356, d112122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d92315 q = 1) (hb : d94357 q = 1) : d112123 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94357, d112123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94357, d112123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d92315 q = 1) (hb : d94358 q = 1) : d112124 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94358, d112124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d94358, d112124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d92315 q = 1) (hb : d94362 q = 1) : d112128 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94362, d112128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94362, d112128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20609 q ha hb
  have h13 (q : Pattern) (ha : d1371 q = 1) (hb : d92315 q = 1) : d1371 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d92315 q = 1) (hb : d94363 q = 1) : d112129 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94363, d112129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d94363, d112129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d92315 q = 1) (hb : d94364 q = 1) : d112130 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94364, d112130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d94364, d112130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d92315 q = 1) (hb : d94365 q = 1) : d112131 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94365, d112131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d94365, d112131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d92315 q = 1) (hb : d94366 q = 1) : d112132 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94366, d112132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94366, d112132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d92315 q = 1) (hb : d94372 q = 1) : d112157 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94372, d112157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94372, d112157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20615 q ha hb
  have h19 (q : Pattern) (ha : d1504 q = 1) (hb : d92315 q = 1) : d1504 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d92315 q = 1) (hb : d94373 q = 1) : d112158 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94373, d112158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d94373, d112158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d92315 q = 1) (hb : d94374 q = 1) : d112159 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94374, d112159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d94374, d112159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d92315 q = 1) (hb : d94375 q = 1) : d112160 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94375, d112160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d94375, d112160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d92315 q = 1) (hb : d94376 q = 1) : d112161 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94376, d112161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d94376, d112161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d92315 q = 1) (hb : d94377 q = 1) : d112162 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94377, d112162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d94377, d112162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro20617 (p : Pattern) (ha : d92315 p = 1) (hb : d94383 p = 1) : d112168 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92315 q = 1) (hb : d94378 q = 1) : d112163 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94378, d112163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94378, d112163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20616 q ha hb
  have h2 (q : Pattern) (ha : d92315 q = 1) (hb : d94379 q = 1) : d112164 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94379, d112164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94379, d112164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92315 q = 1) (hb : d94380 q = 1) : d112165 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94380, d112165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94380, d112165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92315 q = 1) (hb : d94381 q = 1) : d112166 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94381, d112166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94381, d112166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d94382 q = 1) : d112167 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94382, d112167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94382, d112167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d94383 q = 1) : d112168 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94383, d112168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94383, d112168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20618 (p : Pattern) (ha : d8911 p = 1) (hb : d92315 p = 1) : d99028 p = 1 := by
  have h0 (q : Pattern) (ha : d7034 q = 1) (hb : d92313 q = 1) : d7034 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1607 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8910 q = 1) (hb : d92315 q = 1) : d99027 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8910, d92315, d99027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8910, d92315, d99027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8911 q = 1) (hb : d92315 q = 1) : d99028 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8911, d99028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8911, d99028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro20619 (p : Pattern) (ha : d8917 p = 1) (hb : d92315 p = 1) : d112175 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8912 q = 1) (hb : d92315 q = 1) : d99029 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8912, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20618 q ha hb
    | true =>
      simp only [d8912, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8913 q = 1) (hb : d92315 q = 1) : d99030 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8913, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8913, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1615 q = 1) (hb : d92315 q = 1) : d1615 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8914 q = 1) (hb : d92315 q = 1) : d112172 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8914, d112172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8914, d112172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8915 q = 1) (hb : d92315 q = 1) : d112173 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8915, d112173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8915, d112173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8916 q = 1) (hb : d92315 q = 1) : d112174 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8916, d112174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8916, d112174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8917 q = 1) (hb : d92315 q = 1) : d112175 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8917, d112175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8917, d112175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro20620 (p : Pattern) (ha : d8923 p = 1) (hb : d92315 p = 1) : d112181 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1623 q = 1) (hb : d92315 q = 1) : d1623 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8918 q = 1) (hb : d92315 q = 1) : d112176 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8918, d112176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20619 q ha hb
    | true =>
      simp only [d8918, d112176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8919 q = 1) (hb : d92315 q = 1) : d112177 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8919, d112177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8919, d112177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8920 q = 1) (hb : d92315 q = 1) : d112178 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8920, d112178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8920, d112178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8921 q = 1) (hb : d92315 q = 1) : d112179 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8921, d112179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8921, d112179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8922 q = 1) (hb : d92315 q = 1) : d112180 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8922, d112180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8922, d112180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8923 q = 1) (hb : d92315 q = 1) : d112181 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8923, d112181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8923, d112181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro20621 (p : Pattern) (ha : d8926 p = 1) (hb : d92315 p = 1) : d112184 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8912 q = 1) (hb : d92315 q = 1) : d99029 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8912, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20618 q ha hb
    | true =>
      simp only [d8912, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8913 q = 1) (hb : d92315 q = 1) : d99030 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8913, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8913, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1615 q = 1) (hb : d92315 q = 1) : d1615 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8914 q = 1) (hb : d92315 q = 1) : d112172 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8914, d112172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8914, d112172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8915 q = 1) (hb : d92315 q = 1) : d112173 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8915, d112173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8915, d112173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8916 q = 1) (hb : d92315 q = 1) : d112174 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8916, d112174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8916, d112174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8926 q = 1) (hb : d92315 q = 1) : d112184 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8926, d112184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8926, d112184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro20622 (p : Pattern) (ha : d8932 p = 1) (hb : d92315 p = 1) : d112190 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1623 q = 1) (hb : d92315 q = 1) : d1623 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8918 q = 1) (hb : d92315 q = 1) : d112176 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8918, d112176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20619 q ha hb
    | true =>
      simp only [d8918, d112176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8919 q = 1) (hb : d92315 q = 1) : d112177 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8919, d112177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8919, d112177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8920 q = 1) (hb : d92315 q = 1) : d112178 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8920, d112178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8920, d112178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8921 q = 1) (hb : d92315 q = 1) : d112179 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8921, d112179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8921, d112179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8922 q = 1) (hb : d92315 q = 1) : d112180 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8922, d112180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8922, d112180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1633 q = 1) (hb : d92315 q = 1) : d1633 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d8927 q = 1) (hb : d92315 q = 1) : d112185 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8927, d112185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20621 q ha hb
    | true =>
      simp only [d8927, d112185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d8928 q = 1) (hb : d92315 q = 1) : d112186 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8928, d112186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8928, d112186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d8929 q = 1) (hb : d92315 q = 1) : d112187 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8929, d112187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d8929, d112187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d8930 q = 1) (hb : d92315 q = 1) : d112188 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8930, d112188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8930, d112188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d8931 q = 1) (hb : d92315 q = 1) : d112189 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8931, d112189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8931, d112189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d8932 q = 1) (hb : d92315 q = 1) : d112190 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8932, d112190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8932, d112190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro20623 (p : Pattern) (ha : d8960 p = 1) (hb : d92315 p = 1) : d112175 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7037 q = 1) (hb : d92315 q = 1) : d99029 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7037, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14078 q ha hb
    | true =>
      simp only [d7037, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7038 q = 1) (hb : d92315 q = 1) : d99030 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7038, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7038, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1615 q = 1) (hb : d92315 q = 1) : d1615 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8957 q = 1) (hb : d92315 q = 1) : d112172 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8957, d112172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8957, d112172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8958 q = 1) (hb : d92315 q = 1) : d112173 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8958, d112173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8958, d112173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8959 q = 1) (hb : d92315 q = 1) : d112174 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8959, d112174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8959, d112174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8960 q = 1) (hb : d92315 q = 1) : d112175 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8960, d112175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8960, d112175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro20624 (p : Pattern) (ha : d9011 p = 1) (hb : d92315 p = 1) : d112246 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1623 q = 1) (hb : d92315 q = 1) : d1623 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9006 q = 1) (hb : d92315 q = 1) : d112176 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9006, d112176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20623 q ha hb
    | true =>
      simp only [d9006, d112176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9007 q = 1) (hb : d92315 q = 1) : d112177 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9007, d112177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9007, d112177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9008 q = 1) (hb : d92315 q = 1) : d112178 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9008, d112178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9008, d112178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9009 q = 1) (hb : d92315 q = 1) : d112179 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9009, d112179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9009, d112179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9010 q = 1) (hb : d92315 q = 1) : d112180 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d9010, d112180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9010, d112180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1831 q = 1) (hb : d92315 q = 1) : d1831 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d9011 q = 1) (hb : d92315 q = 1) : d112246 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d9011, d112246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9011, d112246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20625 (p : Pattern) (ha : d8937 p = 1) (hb : d92315 p = 1) : d112195 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8912 q = 1) (hb : d92315 q = 1) : d99029 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8912, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20618 q ha hb
    | true =>
      simp only [d8912, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8913 q = 1) (hb : d92315 q = 1) : d99030 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8913, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8913, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1615 q = 1) (hb : d92315 q = 1) : d1615 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8914 q = 1) (hb : d92315 q = 1) : d112172 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8914, d112172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8914, d112172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8915 q = 1) (hb : d92315 q = 1) : d112173 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8915, d112173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8915, d112173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8936 q = 1) (hb : d92315 q = 1) : d112194 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8936, d112194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8936, d112194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8937 q = 1) (hb : d92315 q = 1) : d112195 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8937, d112195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8937, d112195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro20626 (p : Pattern) (ha : d8944 p = 1) (hb : d92315 p = 1) : d112202 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8912 q = 1) (hb : d92315 q = 1) : d99029 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8912, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20618 q ha hb
    | true =>
      simp only [d8912, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8913 q = 1) (hb : d92315 q = 1) : d99030 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8913, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8913, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1615 q = 1) (hb : d92315 q = 1) : d1615 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8914 q = 1) (hb : d92315 q = 1) : d112172 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8914, d112172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8914, d112172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8942 q = 1) (hb : d92315 q = 1) : d112200 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8942, d112200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8942, d112200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8943 q = 1) (hb : d92315 q = 1) : d112201 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8943, d112201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8943, d112201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8944 q = 1) (hb : d92315 q = 1) : d112202 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8944, d112202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8944, d112202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro20627 (p : Pattern) (ha : d8950 p = 1) (hb : d92315 p = 1) : d112207 p = 1 := by
  have h0 (q : Pattern) (ha : d8948 q = 1) (hb : d92313 q = 1) : d8948 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7034 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8949 q = 1) (hb : d92315 q = 1) : d112206 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8949, d92315, d112206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8949, d92315, d112206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8950 q = 1) (hb : d92315 q = 1) : d112207 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8950, d112207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8950, d112207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro20628 (p : Pattern) (ha : d8956 p = 1) (hb : d92315 p = 1) : d112213 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8951 q = 1) (hb : d92315 q = 1) : d112208 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8951, d112208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20627 q ha hb
    | true =>
      simp only [d8951, d112208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8952 q = 1) (hb : d92315 q = 1) : d112209 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8952, d112209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8952, d112209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7037 q = 1) (hb : d92315 q = 1) : d99029 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7037, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14078 q ha hb
    | true =>
      simp only [d7037, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7038 q = 1) (hb : d92315 q = 1) : d99030 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7038, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7038, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8953 q = 1) (hb : d92315 q = 1) : d112210 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8953, d112210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8953, d112210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8954 q = 1) (hb : d92315 q = 1) : d112211 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8954, d112211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8954, d112211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8955 q = 1) (hb : d92315 q = 1) : d112212 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8955, d112212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8955, d112212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8956 q = 1) (hb : d92315 q = 1) : d112213 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8956, d112213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8956, d112213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20629 (p : Pattern) (ha : d8976 p = 1) (hb : d92315 p = 1) : d112219 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8912 q = 1) (hb : d92315 q = 1) : d99029 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8912, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20618 q ha hb
    | true =>
      simp only [d8912, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8913 q = 1) (hb : d92315 q = 1) : d99030 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8913, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8913, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8973 q = 1) (hb : d92315 q = 1) : d112216 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8973, d112216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8973, d112216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8974 q = 1) (hb : d92315 q = 1) : d112217 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8974, d112217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8974, d112217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8975 q = 1) (hb : d92315 q = 1) : d112218 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8975, d112218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8975, d112218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8976 q = 1) (hb : d92315 q = 1) : d112219 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8976, d112219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8976, d112219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20630 (p : Pattern) (ha : d92315 p = 1) (hb : d94391 p = 1) : d112225 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1646 q = 1) (hb : d92315 q = 1) : d1646 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8938 q = 1) (hb : d92315 q = 1) : d112196 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8938, d112196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20625 q ha hb
    | true =>
      simp only [d8938, d112196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8939 q = 1) (hb : d92315 q = 1) : d112197 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8939, d112197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8939, d112197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8940 q = 1) (hb : d92315 q = 1) : d112198 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8940, d112198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8940, d112198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8941 q = 1) (hb : d92315 q = 1) : d112199 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8941, d112199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8941, d112199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1656 q = 1) (hb : d92315 q = 1) : d1656 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d8945 q = 1) (hb : d92315 q = 1) : d112203 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8945, d112203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20626 q ha hb
    | true =>
      simp only [d8945, d112203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8946 q = 1) (hb : d92315 q = 1) : d112204 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8946, d112204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8946, d112204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d8947 q = 1) (hb : d92315 q = 1) : d112205 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8947, d112205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d8947, d112205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d8961 q = 1) (hb : d92315 q = 1) : d112214 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8961, d112214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20628 q ha hb
    | true =>
      simp only [d8961, d112214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20623 q ha hb
  have h11 (q : Pattern) (ha : d92315 q = 1) (hb : d94387 q = 1) : d112215 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94387, d112215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d94387, d112215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d8977 q = 1) (hb : d92315 q = 1) : d112220 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8977, d112220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20629 q ha hb
    | true =>
      simp only [d8977, d112220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d8978 q = 1) (hb : d92315 q = 1) : d112221 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8978, d112221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d8978, d112221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d92315 q = 1) (hb : d94388 q = 1) : d112222 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94388, d112222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94388, d112222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d92315 q = 1) (hb : d94389 q = 1) : d112223 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94389, d112223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d94389, d112223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d92315 q = 1) (hb : d94390 q = 1) : d112224 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94390, d112224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d94390, d112224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d92315 q = 1) (hb : d94391 q = 1) : d112225 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94391, d112225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94391, d112225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro20631 (p : Pattern) (ha : d8983 p = 1) (hb : d92315 p = 1) : d112226 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8912 q = 1) (hb : d92315 q = 1) : d99029 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8912, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20618 q ha hb
    | true =>
      simp only [d8912, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8913 q = 1) (hb : d92315 q = 1) : d99030 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8913, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8913, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1615 q = 1) (hb : d92315 q = 1) : d1615 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8914 q = 1) (hb : d92315 q = 1) : d112172 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8914, d112172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8914, d112172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8915 q = 1) (hb : d92315 q = 1) : d112173 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8915, d112173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8915, d112173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8936 q = 1) (hb : d92315 q = 1) : d112194 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8936, d112194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8936, d112194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8983 q = 1) (hb : d92315 q = 1) : d112226 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8983, d112226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8983, d112226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro20632 (p : Pattern) (ha : d8988 p = 1) (hb : d92315 p = 1) : d112231 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8912 q = 1) (hb : d92315 q = 1) : d99029 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8912, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20618 q ha hb
    | true =>
      simp only [d8912, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8913 q = 1) (hb : d92315 q = 1) : d99030 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8913, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8913, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1615 q = 1) (hb : d92315 q = 1) : d1615 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8914 q = 1) (hb : d92315 q = 1) : d112172 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8914, d112172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8914, d112172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8942 q = 1) (hb : d92315 q = 1) : d112200 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8942, d112200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8942, d112200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8943 q = 1) (hb : d92315 q = 1) : d112201 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8943, d112201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8943, d112201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8988 q = 1) (hb : d92315 q = 1) : d112231 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8988, d112231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8988, d112231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro20633 (p : Pattern) (ha : d8992 p = 1) (hb : d92315 p = 1) : d112235 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8951 q = 1) (hb : d92315 q = 1) : d112208 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8951, d112208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20627 q ha hb
    | true =>
      simp only [d8951, d112208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8952 q = 1) (hb : d92315 q = 1) : d112209 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8952, d112209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8952, d112209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7037 q = 1) (hb : d92315 q = 1) : d99029 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7037, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14078 q ha hb
    | true =>
      simp only [d7037, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7038 q = 1) (hb : d92315 q = 1) : d99030 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7038, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7038, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8953 q = 1) (hb : d92315 q = 1) : d112210 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8953, d112210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8953, d112210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8954 q = 1) (hb : d92315 q = 1) : d112211 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8954, d112211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8954, d112211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8955 q = 1) (hb : d92315 q = 1) : d112212 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8955, d112212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8955, d112212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8992 q = 1) (hb : d92315 q = 1) : d112235 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8992, d112235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8992, d112235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro20634 (p : Pattern) (ha : d8993 p = 1) (hb : d92315 p = 1) : d112184 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7037 q = 1) (hb : d92315 q = 1) : d99029 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7037, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14078 q ha hb
    | true =>
      simp only [d7037, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7038 q = 1) (hb : d92315 q = 1) : d99030 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7038, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7038, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1615 q = 1) (hb : d92315 q = 1) : d1615 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8957 q = 1) (hb : d92315 q = 1) : d112172 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8957, d112172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8957, d112172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8958 q = 1) (hb : d92315 q = 1) : d112173 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8958, d112173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8958, d112173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8959 q = 1) (hb : d92315 q = 1) : d112174 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8959, d112174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8959, d112174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8993 q = 1) (hb : d92315 q = 1) : d112184 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8993, d112184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8993, d112184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro20635 (p : Pattern) (ha : d8998 p = 1) (hb : d92315 p = 1) : d112238 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8912 q = 1) (hb : d92315 q = 1) : d99029 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8912, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20618 q ha hb
    | true =>
      simp only [d8912, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8913 q = 1) (hb : d92315 q = 1) : d99030 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8913, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8913, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8973 q = 1) (hb : d92315 q = 1) : d112216 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8973, d112216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8973, d112216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8974 q = 1) (hb : d92315 q = 1) : d112217 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8974, d112217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8974, d112217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8975 q = 1) (hb : d92315 q = 1) : d112218 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8975, d112218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8975, d112218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8998 q = 1) (hb : d92315 q = 1) : d112238 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8998, d112238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8998, d112238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro20636 (p : Pattern) (ha : d92315 p = 1) (hb : d94396 p = 1) : d112244 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1646 q = 1) (hb : d92315 q = 1) : d1646 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8938 q = 1) (hb : d92315 q = 1) : d112196 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8938, d112196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20625 q ha hb
    | true =>
      simp only [d8938, d112196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8939 q = 1) (hb : d92315 q = 1) : d112197 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8939, d112197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8939, d112197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8940 q = 1) (hb : d92315 q = 1) : d112198 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8940, d112198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8940, d112198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8941 q = 1) (hb : d92315 q = 1) : d112199 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8941, d112199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8941, d112199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1656 q = 1) (hb : d92315 q = 1) : d1656 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d8945 q = 1) (hb : d92315 q = 1) : d112203 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8945, d112203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20626 q ha hb
    | true =>
      simp only [d8945, d112203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8946 q = 1) (hb : d92315 q = 1) : d112204 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8946, d112204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8946, d112204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d8947 q = 1) (hb : d92315 q = 1) : d112205 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8947, d112205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d8947, d112205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d8961 q = 1) (hb : d92315 q = 1) : d112214 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8961, d112214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20628 q ha hb
    | true =>
      simp only [d8961, d112214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20623 q ha hb
  have h11 (q : Pattern) (ha : d92315 q = 1) (hb : d94387 q = 1) : d112215 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94387, d112215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d94387, d112215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d8977 q = 1) (hb : d92315 q = 1) : d112220 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8977, d112220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20629 q ha hb
    | true =>
      simp only [d8977, d112220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d8978 q = 1) (hb : d92315 q = 1) : d112221 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8978, d112221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d8978, d112221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d92315 q = 1) (hb : d94388 q = 1) : d112222 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94388, d112222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94388, d112222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d92315 q = 1) (hb : d94389 q = 1) : d112223 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94389, d112223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d94389, d112223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d92315 q = 1) (hb : d94390 q = 1) : d112224 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94390, d112224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d94390, d112224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d1804 q = 1) (hb : d92315 q = 1) : d1804 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d8984 q = 1) (hb : d92315 q = 1) : d112227 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8984, d112227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20631 q ha hb
    | true =>
      simp only [d8984, d112227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d8985 q = 1) (hb : d92315 q = 1) : d112228 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8985, d112228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8985, d112228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d8986 q = 1) (hb : d92315 q = 1) : d112229 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8986, d112229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d8986, d112229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d8987 q = 1) (hb : d92315 q = 1) : d112230 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8987, d112230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8987, d112230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d1810 q = 1) (hb : d92315 q = 1) : d1810 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d8989 q = 1) (hb : d92315 q = 1) : d112232 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8989, d112232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20632 q ha hb
    | true =>
      simp only [d8989, d112232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d8990 q = 1) (hb : d92315 q = 1) : d112233 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8990, d112233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8990, d112233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d8991 q = 1) (hb : d92315 q = 1) : d112234 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8991, d112234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d8991, d112234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d8994 q = 1) (hb : d92315 q = 1) : d112236 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8994, d112236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20633 q ha hb
    | true =>
      simp only [d8994, d112236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20634 q ha hb
  have h27 (q : Pattern) (ha : d92315 q = 1) (hb : d94392 q = 1) : d112237 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94392, d112237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q hb ha
    | true =>
      simp only [d94392, d112237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d8999 q = 1) (hb : d92315 q = 1) : d112239 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8999, d112239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20635 q ha hb
    | true =>
      simp only [d8999, d112239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d9000 q = 1) (hb : d92315 q = 1) : d112240 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9000, d112240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d9000, d112240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d92315 q = 1) (hb : d94393 q = 1) : d112241 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94393, d112241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d94393, d112241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q hb ha
  have h31 (q : Pattern) (ha : d92315 q = 1) (hb : d94394 q = 1) : d112242 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94394, d112242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
    | true =>
      simp only [d94394, d112242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d92315 q = 1) (hb : d94395 q = 1) : d112243 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94395, d112243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d94395, d112243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d92315 q = 1) (hb : d94396 q = 1) : d112244 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94396, d112244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d94396, d112244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro20637 (p : Pattern) (ha : d92315 p = 1) (hb : d94403 p = 1) : d112253 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8994 q = 1) (hb : d92315 q = 1) : d112236 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8994, d112236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20633 q ha hb
    | true =>
      simp only [d8994, d112236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20634 q ha hb
  have h2 (q : Pattern) (ha : d92315 q = 1) (hb : d94392 q = 1) : d112237 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94392, d112237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94392, d112237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d8999 q = 1) (hb : d92315 q = 1) : d112239 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8999, d112239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20635 q ha hb
    | true =>
      simp only [d8999, d112239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9000 q = 1) (hb : d92315 q = 1) : d112240 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9000, d112240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9000, d112240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d94393 q = 1) : d112241 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94393, d112241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94393, d112241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d94401 q = 1) : d112251 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94401, d112251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94401, d112251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92315 q = 1) (hb : d94402 q = 1) : d112252 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94402, d112252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94402, d112252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92315 q = 1) (hb : d94403 q = 1) : d112253 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94403, d112253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94403, d112253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20638 (p : Pattern) (ha : d9026 p = 1) (hb : d92315 p = 1) : d112260 p = 1 := by
  have h0 (q : Pattern) (ha : d9024 q = 1) (hb : d92313 q = 1) : d9024 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7080 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9025 q = 1) (hb : d92315 q = 1) : d112259 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9025, d92315, d112259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9025, d92315, d112259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9026 q = 1) (hb : d92315 q = 1) : d112260 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9026, d112260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9026, d112260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro20639 (p : Pattern) (ha : d9032 p = 1) (hb : d92315 p = 1) : d112266 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9027 q = 1) (hb : d92315 q = 1) : d112261 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9027, d112261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20638 q ha hb
    | true =>
      simp only [d9027, d112261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9028 q = 1) (hb : d92315 q = 1) : d112262 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9028, d112262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9028, d112262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7083 q = 1) (hb : d92315 q = 1) : d99062 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7083, d99062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14089 q ha hb
    | true =>
      simp only [d7083, d99062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7084 q = 1) (hb : d92315 q = 1) : d99063 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7084, d99063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7084, d99063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9029 q = 1) (hb : d92315 q = 1) : d112263 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9029, d112263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9029, d112263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9030 q = 1) (hb : d92315 q = 1) : d112264 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9030, d112264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9030, d112264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9031 q = 1) (hb : d92315 q = 1) : d112265 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9031, d112265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9031, d112265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9032 q = 1) (hb : d92315 q = 1) : d112266 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9032, d112266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9032, d112266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro20640 (p : Pattern) (ha : d9036 p = 1) (hb : d92315 p = 1) : d112270 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7083 q = 1) (hb : d92315 q = 1) : d99062 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7083, d99062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14089 q ha hb
    | true =>
      simp only [d7083, d99062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7084 q = 1) (hb : d92315 q = 1) : d99063 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7084, d99063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7084, d99063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1909 q = 1) (hb : d92315 q = 1) : d1909 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9033 q = 1) (hb : d92315 q = 1) : d112267 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9033, d112267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9033, d112267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9034 q = 1) (hb : d92315 q = 1) : d112268 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9034, d112268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9034, d112268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9035 q = 1) (hb : d92315 q = 1) : d112269 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9035, d112269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9035, d112269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9036 q = 1) (hb : d92315 q = 1) : d112270 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9036, d112270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9036, d112270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro20641 (p : Pattern) (ha : d9050 p = 1) (hb : d92315 p = 1) : d99061 p = 1 := by
  have h0 (q : Pattern) (ha : d7080 q = 1) (hb : d92313 q = 1) : d7080 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1897 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9049 q = 1) (hb : d92315 q = 1) : d99060 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9049, d92315, d99060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9049, d92315, d99060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9050 q = 1) (hb : d92315 q = 1) : d99061 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9050, d99061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9050, d99061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro20642 (p : Pattern) (ha : d9056 p = 1) (hb : d92315 p = 1) : d112276 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9051 q = 1) (hb : d92315 q = 1) : d99062 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9051, d99062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20641 q ha hb
    | true =>
      simp only [d9051, d99062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9052 q = 1) (hb : d92315 q = 1) : d99063 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9052, d99063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9052, d99063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9053 q = 1) (hb : d92315 q = 1) : d112273 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9053, d112273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9053, d112273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9054 q = 1) (hb : d92315 q = 1) : d112274 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9054, d112274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9054, d112274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9055 q = 1) (hb : d92315 q = 1) : d112275 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9055, d112275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9055, d112275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9056 q = 1) (hb : d92315 q = 1) : d112276 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9056, d112276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9056, d112276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro20643 (p : Pattern) (ha : d92315 p = 1) (hb : d94413 p = 1) : d112282 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9037 q = 1) (hb : d92315 q = 1) : d112271 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9037, d112271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20639 q ha hb
    | true =>
      simp only [d9037, d112271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20640 q ha hb
  have h2 (q : Pattern) (ha : d92315 q = 1) (hb : d94409 q = 1) : d112272 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94409, d112272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94409, d112272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d9057 q = 1) (hb : d92315 q = 1) : d112277 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9057, d112277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20642 q ha hb
    | true =>
      simp only [d9057, d112277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9058 q = 1) (hb : d92315 q = 1) : d112278 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9058, d112278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9058, d112278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d94410 q = 1) : d112279 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94410, d112279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94410, d112279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d94411 q = 1) : d112280 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94411, d112280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94411, d112280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92315 q = 1) (hb : d94412 q = 1) : d112281 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94412, d112281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94412, d112281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92315 q = 1) (hb : d94413 q = 1) : d112282 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94413, d112282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94413, d112282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20644 (p : Pattern) (ha : d92315 p = 1) (hb : d94419 p = 1) : d112288 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8924 q = 1) (hb : d92315 q = 1) : d112182 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8924, d112182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8924, d112182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20620 q ha hb
  have h2 (q : Pattern) (ha : d8925 q = 1) (hb : d92315 q = 1) : d112183 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8925, d112183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8925, d112183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8933 q = 1) (hb : d92315 q = 1) : d112191 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8933, d112191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20620 q ha hb
    | true =>
      simp only [d8933, d112191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20622 q ha hb
  have h4 (q : Pattern) (ha : d8934 q = 1) (hb : d92315 q = 1) : d112192 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8934, d112192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8934, d112192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8935 q = 1) (hb : d92315 q = 1) : d112193 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d8935, d112193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8935, d112193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d94397 q = 1) : d112245 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94397, d112245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20630 q ha hb
    | true =>
      simp only [d94397, d112245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20636 q ha hb
  have h7 (q : Pattern) (ha : d1838 q = 1) (hb : d92315 q = 1) : d1838 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d9012 q = 1) (hb : d92315 q = 1) : d112247 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d9012, d112247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20624 q ha hb
    | true =>
      simp only [d9012, d112247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92315 q = 1) (hb : d94398 q = 1) : d112248 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94398, d112248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94398, d112248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d92315 q = 1) (hb : d94399 q = 1) : d112249 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94399, d112249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94399, d112249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d92315 q = 1) (hb : d94400 q = 1) : d112250 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94400, d112250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d94400, d112250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d92315 q = 1) (hb : d94404 q = 1) : d112254 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94404, d112254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94404, d112254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20637 q ha hb
  have h13 (q : Pattern) (ha : d1848 q = 1) (hb : d92315 q = 1) : d1848 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d92315 q = 1) (hb : d94405 q = 1) : d112255 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94405, d112255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d94405, d112255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d92315 q = 1) (hb : d94406 q = 1) : d112256 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94406, d112256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d94406, d112256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d92315 q = 1) (hb : d94407 q = 1) : d112257 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94407, d112257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d94407, d112257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d92315 q = 1) (hb : d94408 q = 1) : d112258 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94408, d112258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94408, d112258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d92315 q = 1) (hb : d94414 q = 1) : d112283 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94414, d112283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94414, d112283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20643 q ha hb
  have h19 (q : Pattern) (ha : d1981 q = 1) (hb : d92315 q = 1) : d1981 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d92315 q = 1) (hb : d94415 q = 1) : d112284 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94415, d112284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d94415, d112284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d92315 q = 1) (hb : d94416 q = 1) : d112285 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94416, d112285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d94416, d112285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d92315 q = 1) (hb : d94417 q = 1) : d112286 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94417, d112286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d94417, d112286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d92315 q = 1) (hb : d94418 q = 1) : d112287 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94418, d112287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d94418, d112287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d92315 q = 1) (hb : d94419 q = 1) : d112288 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94419, d112288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d94419, d112288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro20645 (p : Pattern) (ha : d92315 p = 1) (hb : d94425 p = 1) : d112294 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92315 q = 1) (hb : d94420 q = 1) : d112289 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94420, d112289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94420, d112289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20644 q ha hb
  have h2 (q : Pattern) (ha : d92315 q = 1) (hb : d94421 q = 1) : d112290 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94421, d112290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94421, d112290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92315 q = 1) (hb : d94422 q = 1) : d112291 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94422, d112291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94422, d112291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92315 q = 1) (hb : d94423 q = 1) : d112292 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94423, d112292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94423, d112292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d94424 q = 1) : d112293 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94424, d112293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94424, d112293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d94425 q = 1) : d112294 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94425, d112294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94425, d112294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20646 (p : Pattern) (ha : d9080 p = 1) (hb : d92315 p = 1) : d99091 p = 1 := by
  have h0 (q : Pattern) (ha : d7115 q = 1) (hb : d92313 q = 1) : d7115 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2090 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9079 q = 1) (hb : d92315 q = 1) : d99090 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9079, d92315, d99090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9079, d92315, d99090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9080 q = 1) (hb : d92315 q = 1) : d99091 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9080, d99091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9080, d99091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro20647 (p : Pattern) (ha : d9086 p = 1) (hb : d92315 p = 1) : d112302 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9081 q = 1) (hb : d92315 q = 1) : d99092 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9081, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20646 q ha hb
    | true =>
      simp only [d9081, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9082 q = 1) (hb : d92315 q = 1) : d99093 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9082, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9082, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2098 q = 1) (hb : d92315 q = 1) : d2098 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9083 q = 1) (hb : d92315 q = 1) : d112299 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9083, d112299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9083, d112299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9084 q = 1) (hb : d92315 q = 1) : d112300 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9084, d112300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9084, d112300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9085 q = 1) (hb : d92315 q = 1) : d112301 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9085, d112301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9085, d112301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9086 q = 1) (hb : d92315 q = 1) : d112302 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9086, d112302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9086, d112302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro20648 (p : Pattern) (ha : d9092 p = 1) (hb : d92315 p = 1) : d112308 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2106 q = 1) (hb : d92315 q = 1) : d2106 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9087 q = 1) (hb : d92315 q = 1) : d112303 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9087, d112303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20647 q ha hb
    | true =>
      simp only [d9087, d112303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9088 q = 1) (hb : d92315 q = 1) : d112304 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9088, d112304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9088, d112304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9089 q = 1) (hb : d92315 q = 1) : d112305 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9089, d112305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9089, d112305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9090 q = 1) (hb : d92315 q = 1) : d112306 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9090, d112306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9090, d112306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9091 q = 1) (hb : d92315 q = 1) : d112307 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d9091, d112307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9091, d112307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d9092 q = 1) (hb : d92315 q = 1) : d112308 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d9092, d112308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9092, d112308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro20649 (p : Pattern) (ha : d9095 p = 1) (hb : d92315 p = 1) : d112311 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9081 q = 1) (hb : d92315 q = 1) : d99092 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9081, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20646 q ha hb
    | true =>
      simp only [d9081, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9082 q = 1) (hb : d92315 q = 1) : d99093 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9082, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9082, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2098 q = 1) (hb : d92315 q = 1) : d2098 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9083 q = 1) (hb : d92315 q = 1) : d112299 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9083, d112299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9083, d112299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9084 q = 1) (hb : d92315 q = 1) : d112300 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9084, d112300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9084, d112300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9085 q = 1) (hb : d92315 q = 1) : d112301 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9085, d112301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9085, d112301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9095 q = 1) (hb : d92315 q = 1) : d112311 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9095, d112311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9095, d112311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro20650 (p : Pattern) (ha : d9101 p = 1) (hb : d92315 p = 1) : d112317 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2106 q = 1) (hb : d92315 q = 1) : d2106 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9087 q = 1) (hb : d92315 q = 1) : d112303 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9087, d112303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20647 q ha hb
    | true =>
      simp only [d9087, d112303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9088 q = 1) (hb : d92315 q = 1) : d112304 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9088, d112304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9088, d112304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9089 q = 1) (hb : d92315 q = 1) : d112305 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9089, d112305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9089, d112305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9090 q = 1) (hb : d92315 q = 1) : d112306 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9090, d112306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9090, d112306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9091 q = 1) (hb : d92315 q = 1) : d112307 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d9091, d112307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9091, d112307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2116 q = 1) (hb : d92315 q = 1) : d2116 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d9096 q = 1) (hb : d92315 q = 1) : d112312 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9096, d112312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20649 q ha hb
    | true =>
      simp only [d9096, d112312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d9097 q = 1) (hb : d92315 q = 1) : d112313 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9097, d112313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9097, d112313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9098 q = 1) (hb : d92315 q = 1) : d112314 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9098, d112314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d9098, d112314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d9099 q = 1) (hb : d92315 q = 1) : d112315 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9099, d112315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9099, d112315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d9100 q = 1) (hb : d92315 q = 1) : d112316 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d9100, d112316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9100, d112316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d9101 q = 1) (hb : d92315 q = 1) : d112317 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d9101, d112317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9101, d112317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro20651 (p : Pattern) (ha : d9129 p = 1) (hb : d92315 p = 1) : d112302 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7118 q = 1) (hb : d92315 q = 1) : d99092 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7118, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14104 q ha hb
    | true =>
      simp only [d7118, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7119 q = 1) (hb : d92315 q = 1) : d99093 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7119, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7119, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2098 q = 1) (hb : d92315 q = 1) : d2098 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9126 q = 1) (hb : d92315 q = 1) : d112299 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9126, d112299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9126, d112299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9127 q = 1) (hb : d92315 q = 1) : d112300 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9127, d112300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9127, d112300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9128 q = 1) (hb : d92315 q = 1) : d112301 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9128, d112301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9128, d112301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9129 q = 1) (hb : d92315 q = 1) : d112302 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9129, d112302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9129, d112302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro20652 (p : Pattern) (ha : d9180 p = 1) (hb : d92315 p = 1) : d112373 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2106 q = 1) (hb : d92315 q = 1) : d2106 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9175 q = 1) (hb : d92315 q = 1) : d112303 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9175, d112303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20651 q ha hb
    | true =>
      simp only [d9175, d112303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9176 q = 1) (hb : d92315 q = 1) : d112304 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9176, d112304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9176, d112304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9177 q = 1) (hb : d92315 q = 1) : d112305 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9177, d112305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9177, d112305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9178 q = 1) (hb : d92315 q = 1) : d112306 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9178, d112306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9178, d112306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9179 q = 1) (hb : d92315 q = 1) : d112307 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d9179, d112307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9179, d112307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2309 q = 1) (hb : d92315 q = 1) : d2309 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d9180 q = 1) (hb : d92315 q = 1) : d112373 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d9180, d112373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9180, d112373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20653 (p : Pattern) (ha : d9106 p = 1) (hb : d92315 p = 1) : d112322 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9081 q = 1) (hb : d92315 q = 1) : d99092 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9081, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20646 q ha hb
    | true =>
      simp only [d9081, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9082 q = 1) (hb : d92315 q = 1) : d99093 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9082, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9082, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2098 q = 1) (hb : d92315 q = 1) : d2098 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9083 q = 1) (hb : d92315 q = 1) : d112299 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9083, d112299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9083, d112299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9084 q = 1) (hb : d92315 q = 1) : d112300 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9084, d112300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9084, d112300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9105 q = 1) (hb : d92315 q = 1) : d112321 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9105, d112321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9105, d112321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d9106 q = 1) (hb : d92315 q = 1) : d112322 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9106, d112322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9106, d112322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro20654 (p : Pattern) (ha : d9113 p = 1) (hb : d92315 p = 1) : d112329 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9081 q = 1) (hb : d92315 q = 1) : d99092 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9081, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20646 q ha hb
    | true =>
      simp only [d9081, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9082 q = 1) (hb : d92315 q = 1) : d99093 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9082, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9082, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2098 q = 1) (hb : d92315 q = 1) : d2098 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9083 q = 1) (hb : d92315 q = 1) : d112299 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9083, d112299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9083, d112299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9111 q = 1) (hb : d92315 q = 1) : d112327 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9111, d112327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9111, d112327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9112 q = 1) (hb : d92315 q = 1) : d112328 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9112, d112328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9112, d112328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9113 q = 1) (hb : d92315 q = 1) : d112329 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9113, d112329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9113, d112329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro20655 (p : Pattern) (ha : d9119 p = 1) (hb : d92315 p = 1) : d112334 p = 1 := by
  have h0 (q : Pattern) (ha : d9117 q = 1) (hb : d92313 q = 1) : d9117 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7115 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9118 q = 1) (hb : d92315 q = 1) : d112333 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9118, d92315, d112333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9118, d92315, d112333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9119 q = 1) (hb : d92315 q = 1) : d112334 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9119, d112334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9119, d112334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro20656 (p : Pattern) (ha : d9125 p = 1) (hb : d92315 p = 1) : d112340 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9120 q = 1) (hb : d92315 q = 1) : d112335 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9120, d112335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20655 q ha hb
    | true =>
      simp only [d9120, d112335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9121 q = 1) (hb : d92315 q = 1) : d112336 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9121, d112336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9121, d112336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7118 q = 1) (hb : d92315 q = 1) : d99092 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7118, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14104 q ha hb
    | true =>
      simp only [d7118, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7119 q = 1) (hb : d92315 q = 1) : d99093 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7119, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7119, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9122 q = 1) (hb : d92315 q = 1) : d112337 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9122, d112337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9122, d112337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9123 q = 1) (hb : d92315 q = 1) : d112338 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9123, d112338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9123, d112338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9124 q = 1) (hb : d92315 q = 1) : d112339 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9124, d112339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9124, d112339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9125 q = 1) (hb : d92315 q = 1) : d112340 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9125, d112340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9125, d112340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20657 (p : Pattern) (ha : d9145 p = 1) (hb : d92315 p = 1) : d112346 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9081 q = 1) (hb : d92315 q = 1) : d99092 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9081, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20646 q ha hb
    | true =>
      simp only [d9081, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9082 q = 1) (hb : d92315 q = 1) : d99093 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9082, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9082, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9142 q = 1) (hb : d92315 q = 1) : d112343 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9142, d112343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9142, d112343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9143 q = 1) (hb : d92315 q = 1) : d112344 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9143, d112344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9143, d112344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9144 q = 1) (hb : d92315 q = 1) : d112345 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9144, d112345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9144, d112345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9145 q = 1) (hb : d92315 q = 1) : d112346 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9145, d112346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9145, d112346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20658 (p : Pattern) (ha : d92315 p = 1) (hb : d94434 p = 1) : d112352 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2129 q = 1) (hb : d92315 q = 1) : d2129 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9107 q = 1) (hb : d92315 q = 1) : d112323 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9107, d112323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20653 q ha hb
    | true =>
      simp only [d9107, d112323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9108 q = 1) (hb : d92315 q = 1) : d112324 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9108, d112324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9108, d112324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9109 q = 1) (hb : d92315 q = 1) : d112325 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9109, d112325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9109, d112325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9110 q = 1) (hb : d92315 q = 1) : d112326 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9110, d112326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9110, d112326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2139 q = 1) (hb : d92315 q = 1) : d2139 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d9114 q = 1) (hb : d92315 q = 1) : d112330 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9114, d112330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20654 q ha hb
    | true =>
      simp only [d9114, d112330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9115 q = 1) (hb : d92315 q = 1) : d112331 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9115, d112331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9115, d112331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d9116 q = 1) (hb : d92315 q = 1) : d112332 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9116, d112332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9116, d112332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d9130 q = 1) (hb : d92315 q = 1) : d112341 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9130, d112341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20656 q ha hb
    | true =>
      simp only [d9130, d112341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20651 q ha hb
  have h11 (q : Pattern) (ha : d92315 q = 1) (hb : d94430 q = 1) : d112342 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94430, d112342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d94430, d112342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d9146 q = 1) (hb : d92315 q = 1) : d112347 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9146, d112347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20657 q ha hb
    | true =>
      simp only [d9146, d112347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d9147 q = 1) (hb : d92315 q = 1) : d112348 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9147, d112348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d9147, d112348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d92315 q = 1) (hb : d94431 q = 1) : d112349 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94431, d112349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94431, d112349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d92315 q = 1) (hb : d94432 q = 1) : d112350 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94432, d112350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d94432, d112350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d92315 q = 1) (hb : d94433 q = 1) : d112351 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94433, d112351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d94433, d112351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d92315 q = 1) (hb : d94434 q = 1) : d112352 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94434, d112352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94434, d112352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro20659 (p : Pattern) (ha : d9152 p = 1) (hb : d92315 p = 1) : d112353 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9081 q = 1) (hb : d92315 q = 1) : d99092 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9081, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20646 q ha hb
    | true =>
      simp only [d9081, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9082 q = 1) (hb : d92315 q = 1) : d99093 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9082, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9082, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2098 q = 1) (hb : d92315 q = 1) : d2098 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9083 q = 1) (hb : d92315 q = 1) : d112299 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9083, d112299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9083, d112299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9084 q = 1) (hb : d92315 q = 1) : d112300 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9084, d112300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9084, d112300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9105 q = 1) (hb : d92315 q = 1) : d112321 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9105, d112321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9105, d112321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d9152 q = 1) (hb : d92315 q = 1) : d112353 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9152, d112353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9152, d112353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro20660 (p : Pattern) (ha : d9157 p = 1) (hb : d92315 p = 1) : d112358 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9081 q = 1) (hb : d92315 q = 1) : d99092 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9081, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20646 q ha hb
    | true =>
      simp only [d9081, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9082 q = 1) (hb : d92315 q = 1) : d99093 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9082, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9082, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2098 q = 1) (hb : d92315 q = 1) : d2098 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9083 q = 1) (hb : d92315 q = 1) : d112299 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9083, d112299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9083, d112299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9111 q = 1) (hb : d92315 q = 1) : d112327 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9111, d112327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9111, d112327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9112 q = 1) (hb : d92315 q = 1) : d112328 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9112, d112328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9112, d112328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9157 q = 1) (hb : d92315 q = 1) : d112358 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9157, d112358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9157, d112358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro20661 (p : Pattern) (ha : d9161 p = 1) (hb : d92315 p = 1) : d112362 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9120 q = 1) (hb : d92315 q = 1) : d112335 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9120, d112335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20655 q ha hb
    | true =>
      simp only [d9120, d112335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9121 q = 1) (hb : d92315 q = 1) : d112336 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9121, d112336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9121, d112336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7118 q = 1) (hb : d92315 q = 1) : d99092 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7118, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14104 q ha hb
    | true =>
      simp only [d7118, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7119 q = 1) (hb : d92315 q = 1) : d99093 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7119, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7119, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9122 q = 1) (hb : d92315 q = 1) : d112337 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9122, d112337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9122, d112337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9123 q = 1) (hb : d92315 q = 1) : d112338 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9123, d112338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9123, d112338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9124 q = 1) (hb : d92315 q = 1) : d112339 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9124, d112339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9124, d112339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9161 q = 1) (hb : d92315 q = 1) : d112362 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9161, d112362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9161, d112362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro20662 (p : Pattern) (ha : d9162 p = 1) (hb : d92315 p = 1) : d112311 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7118 q = 1) (hb : d92315 q = 1) : d99092 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7118, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14104 q ha hb
    | true =>
      simp only [d7118, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7119 q = 1) (hb : d92315 q = 1) : d99093 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7119, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7119, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2098 q = 1) (hb : d92315 q = 1) : d2098 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9126 q = 1) (hb : d92315 q = 1) : d112299 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9126, d112299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9126, d112299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9127 q = 1) (hb : d92315 q = 1) : d112300 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9127, d112300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9127, d112300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9128 q = 1) (hb : d92315 q = 1) : d112301 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9128, d112301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9128, d112301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9162 q = 1) (hb : d92315 q = 1) : d112311 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9162, d112311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9162, d112311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro20663 (p : Pattern) (ha : d9167 p = 1) (hb : d92315 p = 1) : d112365 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9081 q = 1) (hb : d92315 q = 1) : d99092 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9081, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20646 q ha hb
    | true =>
      simp only [d9081, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9082 q = 1) (hb : d92315 q = 1) : d99093 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9082, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9082, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9142 q = 1) (hb : d92315 q = 1) : d112343 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9142, d112343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9142, d112343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9143 q = 1) (hb : d92315 q = 1) : d112344 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9143, d112344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9143, d112344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9144 q = 1) (hb : d92315 q = 1) : d112345 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9144, d112345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9144, d112345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9167 q = 1) (hb : d92315 q = 1) : d112365 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9167, d112365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9167, d112365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro20664 (p : Pattern) (ha : d92315 p = 1) (hb : d94439 p = 1) : d112371 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2129 q = 1) (hb : d92315 q = 1) : d2129 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9107 q = 1) (hb : d92315 q = 1) : d112323 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9107, d112323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20653 q ha hb
    | true =>
      simp only [d9107, d112323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9108 q = 1) (hb : d92315 q = 1) : d112324 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9108, d112324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9108, d112324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9109 q = 1) (hb : d92315 q = 1) : d112325 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9109, d112325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9109, d112325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9110 q = 1) (hb : d92315 q = 1) : d112326 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9110, d112326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9110, d112326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2139 q = 1) (hb : d92315 q = 1) : d2139 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d9114 q = 1) (hb : d92315 q = 1) : d112330 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9114, d112330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20654 q ha hb
    | true =>
      simp only [d9114, d112330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9115 q = 1) (hb : d92315 q = 1) : d112331 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9115, d112331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9115, d112331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d9116 q = 1) (hb : d92315 q = 1) : d112332 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9116, d112332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9116, d112332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d9130 q = 1) (hb : d92315 q = 1) : d112341 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9130, d112341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20656 q ha hb
    | true =>
      simp only [d9130, d112341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20651 q ha hb
  have h11 (q : Pattern) (ha : d92315 q = 1) (hb : d94430 q = 1) : d112342 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94430, d112342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d94430, d112342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d9146 q = 1) (hb : d92315 q = 1) : d112347 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9146, d112347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20657 q ha hb
    | true =>
      simp only [d9146, d112347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d9147 q = 1) (hb : d92315 q = 1) : d112348 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9147, d112348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d9147, d112348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d92315 q = 1) (hb : d94431 q = 1) : d112349 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94431, d112349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94431, d112349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d92315 q = 1) (hb : d94432 q = 1) : d112350 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94432, d112350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d94432, d112350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d92315 q = 1) (hb : d94433 q = 1) : d112351 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94433, d112351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d94433, d112351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d2282 q = 1) (hb : d92315 q = 1) : d2282 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d9153 q = 1) (hb : d92315 q = 1) : d112354 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9153, d112354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20659 q ha hb
    | true =>
      simp only [d9153, d112354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d9154 q = 1) (hb : d92315 q = 1) : d112355 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9154, d112355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9154, d112355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d9155 q = 1) (hb : d92315 q = 1) : d112356 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9155, d112356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d9155, d112356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d9156 q = 1) (hb : d92315 q = 1) : d112357 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9156, d112357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9156, d112357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d2288 q = 1) (hb : d92315 q = 1) : d2288 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d9158 q = 1) (hb : d92315 q = 1) : d112359 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9158, d112359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20660 q ha hb
    | true =>
      simp only [d9158, d112359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d9159 q = 1) (hb : d92315 q = 1) : d112360 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9159, d112360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9159, d112360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d9160 q = 1) (hb : d92315 q = 1) : d112361 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9160, d112361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d9160, d112361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d9163 q = 1) (hb : d92315 q = 1) : d112363 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9163, d112363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20661 q ha hb
    | true =>
      simp only [d9163, d112363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20662 q ha hb
  have h27 (q : Pattern) (ha : d92315 q = 1) (hb : d94435 q = 1) : d112364 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94435, d112364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q hb ha
    | true =>
      simp only [d94435, d112364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d9168 q = 1) (hb : d92315 q = 1) : d112366 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9168, d112366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20663 q ha hb
    | true =>
      simp only [d9168, d112366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d9169 q = 1) (hb : d92315 q = 1) : d112367 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9169, d112367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d9169, d112367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d92315 q = 1) (hb : d94436 q = 1) : d112368 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94436, d112368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d94436, d112368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q hb ha
  have h31 (q : Pattern) (ha : d92315 q = 1) (hb : d94437 q = 1) : d112369 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94437, d112369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
    | true =>
      simp only [d94437, d112369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d92315 q = 1) (hb : d94438 q = 1) : d112370 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94438, d112370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d94438, d112370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d92315 q = 1) (hb : d94439 q = 1) : d112371 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94439, d112371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d94439, d112371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro20665 (p : Pattern) (ha : d92315 p = 1) (hb : d94446 p = 1) : d112380 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9163 q = 1) (hb : d92315 q = 1) : d112363 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9163, d112363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20661 q ha hb
    | true =>
      simp only [d9163, d112363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20662 q ha hb
  have h2 (q : Pattern) (ha : d92315 q = 1) (hb : d94435 q = 1) : d112364 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94435, d112364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94435, d112364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d9168 q = 1) (hb : d92315 q = 1) : d112366 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9168, d112366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20663 q ha hb
    | true =>
      simp only [d9168, d112366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9169 q = 1) (hb : d92315 q = 1) : d112367 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9169, d112367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9169, d112367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d94436 q = 1) : d112368 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94436, d112368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94436, d112368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d94444 q = 1) : d112378 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94444, d112378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94444, d112378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92315 q = 1) (hb : d94445 q = 1) : d112379 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94445, d112379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94445, d112379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92315 q = 1) (hb : d94446 q = 1) : d112380 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94446, d112380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94446, d112380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20666 (p : Pattern) (ha : d9195 p = 1) (hb : d92315 p = 1) : d112387 p = 1 := by
  have h0 (q : Pattern) (ha : d9193 q = 1) (hb : d92313 q = 1) : d9193 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7161 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9194 q = 1) (hb : d92315 q = 1) : d112386 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9194, d92315, d112386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9194, d92315, d112386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9195 q = 1) (hb : d92315 q = 1) : d112387 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9195, d112387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9195, d112387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro20667 (p : Pattern) (ha : d9201 p = 1) (hb : d92315 p = 1) : d112393 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9196 q = 1) (hb : d92315 q = 1) : d112388 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9196, d112388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20666 q ha hb
    | true =>
      simp only [d9196, d112388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9197 q = 1) (hb : d92315 q = 1) : d112389 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9197, d112389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9197, d112389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7164 q = 1) (hb : d92315 q = 1) : d99125 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7164, d99125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14115 q ha hb
    | true =>
      simp only [d7164, d99125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7165 q = 1) (hb : d92315 q = 1) : d99126 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7165, d99126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7165, d99126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9198 q = 1) (hb : d92315 q = 1) : d112390 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9198, d112390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9198, d112390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9199 q = 1) (hb : d92315 q = 1) : d112391 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9199, d112391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9199, d112391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9200 q = 1) (hb : d92315 q = 1) : d112392 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9200, d112392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9200, d112392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9201 q = 1) (hb : d92315 q = 1) : d112393 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9201, d112393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9201, d112393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro20668 (p : Pattern) (ha : d9205 p = 1) (hb : d92315 p = 1) : d112397 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7164 q = 1) (hb : d92315 q = 1) : d99125 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7164, d99125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14115 q ha hb
    | true =>
      simp only [d7164, d99125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7165 q = 1) (hb : d92315 q = 1) : d99126 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7165, d99126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7165, d99126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2387 q = 1) (hb : d92315 q = 1) : d2387 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9202 q = 1) (hb : d92315 q = 1) : d112394 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9202, d112394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9202, d112394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9203 q = 1) (hb : d92315 q = 1) : d112395 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9203, d112395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9203, d112395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9204 q = 1) (hb : d92315 q = 1) : d112396 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9204, d112396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9204, d112396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9205 q = 1) (hb : d92315 q = 1) : d112397 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9205, d112397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9205, d112397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro20669 (p : Pattern) (ha : d9219 p = 1) (hb : d92315 p = 1) : d99124 p = 1 := by
  have h0 (q : Pattern) (ha : d7161 q = 1) (hb : d92313 q = 1) : d7161 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2375 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9218 q = 1) (hb : d92315 q = 1) : d99123 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9218, d92315, d99123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9218, d92315, d99123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9219 q = 1) (hb : d92315 q = 1) : d99124 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9219, d99124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9219, d99124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro20670 (p : Pattern) (ha : d9225 p = 1) (hb : d92315 p = 1) : d112403 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9220 q = 1) (hb : d92315 q = 1) : d99125 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9220, d99125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20669 q ha hb
    | true =>
      simp only [d9220, d99125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9221 q = 1) (hb : d92315 q = 1) : d99126 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9221, d99126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9221, d99126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9222 q = 1) (hb : d92315 q = 1) : d112400 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9222, d112400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9222, d112400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9223 q = 1) (hb : d92315 q = 1) : d112401 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9223, d112401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9223, d112401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9224 q = 1) (hb : d92315 q = 1) : d112402 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9224, d112402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9224, d112402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9225 q = 1) (hb : d92315 q = 1) : d112403 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9225, d112403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9225, d112403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro20671 (p : Pattern) (ha : d92315 p = 1) (hb : d94456 p = 1) : d112409 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9206 q = 1) (hb : d92315 q = 1) : d112398 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9206, d112398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20667 q ha hb
    | true =>
      simp only [d9206, d112398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20668 q ha hb
  have h2 (q : Pattern) (ha : d92315 q = 1) (hb : d94452 q = 1) : d112399 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94452, d112399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94452, d112399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d9226 q = 1) (hb : d92315 q = 1) : d112404 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9226, d112404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20670 q ha hb
    | true =>
      simp only [d9226, d112404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9227 q = 1) (hb : d92315 q = 1) : d112405 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9227, d112405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9227, d112405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d94453 q = 1) : d112406 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94453, d112406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94453, d112406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d94454 q = 1) : d112407 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94454, d112407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94454, d112407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92315 q = 1) (hb : d94455 q = 1) : d112408 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94455, d112408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94455, d112408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92315 q = 1) (hb : d94456 q = 1) : d112409 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94456, d112409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94456, d112409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20672 (p : Pattern) (ha : d92315 p = 1) (hb : d94462 p = 1) : d112415 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9093 q = 1) (hb : d92315 q = 1) : d112309 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d9093, d112309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9093, d112309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20648 q ha hb
  have h2 (q : Pattern) (ha : d9094 q = 1) (hb : d92315 q = 1) : d112310 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d9094, d112310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9094, d112310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d9102 q = 1) (hb : d92315 q = 1) : d112318 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d9102, d112318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20648 q ha hb
    | true =>
      simp only [d9102, d112318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20650 q ha hb
  have h4 (q : Pattern) (ha : d9103 q = 1) (hb : d92315 q = 1) : d112319 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d9103, d112319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9103, d112319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9104 q = 1) (hb : d92315 q = 1) : d112320 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d9104, d112320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9104, d112320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d94440 q = 1) : d112372 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94440, d112372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20658 q ha hb
    | true =>
      simp only [d94440, d112372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20664 q ha hb
  have h7 (q : Pattern) (ha : d2316 q = 1) (hb : d92315 q = 1) : d2316 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d9181 q = 1) (hb : d92315 q = 1) : d112374 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d9181, d112374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20652 q ha hb
    | true =>
      simp only [d9181, d112374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92315 q = 1) (hb : d94441 q = 1) : d112375 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94441, d112375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94441, d112375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d92315 q = 1) (hb : d94442 q = 1) : d112376 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94442, d112376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94442, d112376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d92315 q = 1) (hb : d94443 q = 1) : d112377 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94443, d112377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d94443, d112377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d92315 q = 1) (hb : d94447 q = 1) : d112381 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94447, d112381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94447, d112381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20665 q ha hb
  have h13 (q : Pattern) (ha : d2326 q = 1) (hb : d92315 q = 1) : d2326 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d92315 q = 1) (hb : d94448 q = 1) : d112382 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94448, d112382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d94448, d112382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d92315 q = 1) (hb : d94449 q = 1) : d112383 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94449, d112383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d94449, d112383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d92315 q = 1) (hb : d94450 q = 1) : d112384 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94450, d112384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d94450, d112384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d92315 q = 1) (hb : d94451 q = 1) : d112385 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94451, d112385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94451, d112385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d92315 q = 1) (hb : d94457 q = 1) : d112410 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94457, d112410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94457, d112410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20671 q ha hb
  have h19 (q : Pattern) (ha : d2459 q = 1) (hb : d92315 q = 1) : d2459 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d92315 q = 1) (hb : d94458 q = 1) : d112411 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94458, d112411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d94458, d112411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d92315 q = 1) (hb : d94459 q = 1) : d112412 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94459, d112412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d94459, d112412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d92315 q = 1) (hb : d94460 q = 1) : d112413 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94460, d112413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d94460, d112413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d92315 q = 1) (hb : d94461 q = 1) : d112414 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94461, d112414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d94461, d112414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d92315 q = 1) (hb : d94462 q = 1) : d112415 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94462, d112415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d94462, d112415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro20673 (p : Pattern) (ha : d92315 p = 1) (hb : d94468 p = 1) : d112421 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92315 q = 1) (hb : d94463 q = 1) : d112416 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94463, d112416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94463, d112416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20672 q ha hb
  have h2 (q : Pattern) (ha : d92315 q = 1) (hb : d94464 q = 1) : d112417 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94464, d112417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94464, d112417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92315 q = 1) (hb : d94465 q = 1) : d112418 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94465, d112418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94465, d112418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92315 q = 1) (hb : d94466 q = 1) : d112419 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94466, d112419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94466, d112419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d94467 q = 1) : d112420 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94467, d112420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94467, d112420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d94468 q = 1) : d112421 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94468, d112421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94468, d112421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20674 (p : Pattern) (ha : d92315 p = 1) (hb : d94474 p = 1) : d112427 p = 1 := by
  have h0 (q : Pattern) (ha : d92315 q = 1) (hb : d94303 q = 1) : d111920 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d94303, d111920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20535 q ha hb
    | true =>
      simp only [d94303, d111920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20561 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d92315 q = 1) (hb : d94343 q = 1) : d112044 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d94343, d112044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94343, d112044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20589 q ha hb
  have h3 (q : Pattern) (ha : d92315 q = 1) (hb : d94344 q = 1) : d112045 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d94344, d112045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94344, d112045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92315 q = 1) (hb : d94384 q = 1) : d112169 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d94384, d112169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94384, d112169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20617 q ha hb
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d94385 q = 1) : d112170 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d94385, d112170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94385, d112170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d94386 q = 1) : d112171 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d94386, d112171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94386, d112171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92315 q = 1) (hb : d94426 q = 1) : d112295 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d94426, d112295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94426, d112295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20645 q ha hb
  have h8 (q : Pattern) (ha : d92315 q = 1) (hb : d94427 q = 1) : d112296 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d94427, d112296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94427, d112296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92315 q = 1) (hb : d94428 q = 1) : d112297 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d94428, d112297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94428, d112297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d92315 q = 1) (hb : d94429 q = 1) : d112298 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d94429, d112298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94429, d112298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d92315 q = 1) (hb : d94469 q = 1) : d112422 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d94469, d112422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94469, d112422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20673 q ha hb
  have h12 (q : Pattern) (ha : d92315 q = 1) (hb : d94470 q = 1) : d112423 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d94470, d112423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94470, d112423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d92315 q = 1) (hb : d94471 q = 1) : d112424 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d94471, d112424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94471, d112424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d92315 q = 1) (hb : d94472 q = 1) : d112425 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d94472, d112425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94472, d112425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d92315 q = 1) (hb : d94473 q = 1) : d112426 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d94473, d112426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94473, d112426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d92315 q = 1) (hb : d94474 q = 1) : d112427 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d94474, d112427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d94474, d112427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro20675 (p : Pattern) (ha : d92315 p = 1) (hb : d94480 p = 1) : d112433 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92315 q = 1) (hb : d94475 q = 1) : d112428 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d94475, d112428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20674 q ha hb
    | true =>
      simp only [d94475, d112428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92315 q = 1) (hb : d94476 q = 1) : d112429 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d94476, d112429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94476, d112429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d92315 q = 1) (hb : d94477 q = 1) : d112430 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d94477, d112430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94477, d112430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92315 q = 1) (hb : d94478 q = 1) : d112431 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d94478, d112431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94478, d112431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d94479 q = 1) : d112432 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d94479, d112432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94479, d112432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d94480 q = 1) : d112433 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d94480, d112433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94480, d112433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20676 (p : Pattern) (ha : d92315 p = 1) (hb : d94486 p = 1) : d112439 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92315 q = 1) (hb : d94481 q = 1) : d112434 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d94481, d112434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20675 q ha hb
    | true =>
      simp only [d94481, d112434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92315 q = 1) (hb : d94482 q = 1) : d112435 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d94482, d112435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94482, d112435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d92315 q = 1) (hb : d94483 q = 1) : d112436 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d94483, d112436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94483, d112436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92315 q = 1) (hb : d94484 q = 1) : d112437 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d94484, d112437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94484, d112437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d94485 q = 1) : d112438 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d94485, d112438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94485, d112438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d94486 q = 1) : d112439 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d94486, d112439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94486, d112439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20677 (p : Pattern) (ha : d92315 p = 1) (hb : d94492 p = 1) : d112445 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92315 q = 1) (hb : d94487 q = 1) : d112440 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d94487, d112440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20676 q ha hb
    | true =>
      simp only [d94487, d112440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92315 q = 1) (hb : d94488 q = 1) : d112441 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d94488, d112441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94488, d112441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d92315 q = 1) (hb : d94489 q = 1) : d112442 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d94489, d112442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94489, d112442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92315 q = 1) (hb : d94490 q = 1) : d112443 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d94490, d112443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94490, d112443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d94491 q = 1) : d112444 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d94491, d112444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94491, d112444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d94492 q = 1) : d112445 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d94492, d112445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94492, d112445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20678 (p : Pattern) (ha : d92315 p = 1) (hb : d94498 p = 1) : d112451 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92315 q = 1) (hb : d94493 q = 1) : d112446 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d94493, d112446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20677 q ha hb
    | true =>
      simp only [d94493, d112446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92315 q = 1) (hb : d94494 q = 1) : d112447 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d94494, d112447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94494, d112447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d92315 q = 1) (hb : d94495 q = 1) : d112448 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d94495, d112448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94495, d112448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92315 q = 1) (hb : d94496 q = 1) : d112449 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d94496, d112449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94496, d112449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d94497 q = 1) : d112450 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d94497, d112450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94497, d112450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d94498 q = 1) : d112451 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d94498, d112451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94498, d112451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20679 (p : Pattern) (ha : d92315 p = 1) (hb : d94504 p = 1) : d112457 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92315 q = 1) (hb : d94499 q = 1) : d112452 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d94499, d112452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20678 q ha hb
    | true =>
      simp only [d94499, d112452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92315 q = 1) (hb : d94500 q = 1) : d112453 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d94500, d112453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94500, d112453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d92315 q = 1) (hb : d94501 q = 1) : d112454 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d94501, d112454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94501, d112454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92315 q = 1) (hb : d94502 q = 1) : d112455 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d94502, d112455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94502, d112455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d94503 q = 1) : d112456 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d94503, d112456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94503, d112456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d94504 q = 1) : d112457 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d94504, d112457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94504, d112457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20680 (p : Pattern) (ha : d92315 p = 1) (hb : d94510 p = 1) : d112463 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92315 q = 1) (hb : d94505 q = 1) : d112458 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d94505, d112458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20679 q ha hb
    | true =>
      simp only [d94505, d112458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92315 q = 1) (hb : d94506 q = 1) : d112459 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d94506, d112459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94506, d112459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d92315 q = 1) (hb : d94507 q = 1) : d112460 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d94507, d112460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94507, d112460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92315 q = 1) (hb : d94508 q = 1) : d112461 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d94508, d112461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94508, d112461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d94509 q = 1) : d112462 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d94509, d112462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94509, d112462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d94510 q = 1) : d112463 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d94510, d112463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94510, d112463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20681 (p : Pattern) (ha : d92315 p = 1) (hb : d94516 p = 1) : d112469 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92315 q = 1) (hb : d94511 q = 1) : d112464 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d94511, d112464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20680 q ha hb
    | true =>
      simp only [d94511, d112464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92315 q = 1) (hb : d94512 q = 1) : d112465 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d94512, d112465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94512, d112465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d92315 q = 1) (hb : d94513 q = 1) : d112466 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d94513, d112466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94513, d112466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92315 q = 1) (hb : d94514 q = 1) : d112467 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d94514, d112467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94514, d112467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d94515 q = 1) : d112468 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d94515, d112468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94515, d112468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d94516 q = 1) : d112469 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d94516, d112469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94516, d112469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20682 (p : Pattern) (ha : d83670 p = 1) (hb : d111667 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d83665 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d83665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14142 q ha hb
    | true =>
      simp only [d482, d83665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d83666 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d83666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d83666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d83667 q = 1) (hb : d111664 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83667, d111664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d83667, d111664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83668 q = 1) (hb : d111665 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83668, d111665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83668, d111665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d83669 q = 1) (hb : d111666 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83669, d111666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83669, d111666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d83670 q = 1) (hb : d111667 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83670, d111667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83670, d111667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20683 (p : Pattern) (ha : d83676 p = 1) (hb : d111673 p = 1) : d0 p = 1 := by
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
  have h8 (q : Pattern) (ha : d83671 q = 1) (hb : d111668 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83671, d111668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20682 q ha hb
    | true =>
      simp only [d83671, d111668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d83672 q = 1) (hb : d111669 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83672, d111669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d83672, d111669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h13 (q : Pattern) (ha : d83673 q = 1) (hb : d111670 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83673, d111670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d83673, d111670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d83674 q = 1) (hb : d111671 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83674, d111671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d83674, d111671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d83675 q = 1) (hb : d111672 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83675, d111672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d83675, d111672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d83676 q = 1) (hb : d111673 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83676, d111673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83676, d111673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro20684 (p : Pattern) (ha : d83677 p = 1) (hb : d111674 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d83665 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d83665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14142 q ha hb
    | true =>
      simp only [d482, d83665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d83666 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d83666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d83666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d83667 q = 1) (hb : d111664 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83667, d111664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d83667, d111664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83668 q = 1) (hb : d111665 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83668, d111665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83668, d111665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d83669 q = 1) (hb : d111666 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83669, d111666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83669, d111666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d83677 q = 1) (hb : d111674 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83677, d111674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d83677, d111674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20685 (p : Pattern) (ha : d83683 p = 1) (hb : d111680 p = 1) : d0 p = 1 := by
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
  have h8 (q : Pattern) (ha : d83671 q = 1) (hb : d111668 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83671, d111668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20682 q ha hb
    | true =>
      simp only [d83671, d111668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d83672 q = 1) (hb : d111669 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83672, d111669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d83672, d111669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h13 (q : Pattern) (ha : d83673 q = 1) (hb : d111670 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83673, d111670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d83673, d111670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d83674 q = 1) (hb : d111671 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83674, d111671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d83674, d111671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d83675 q = 1) (hb : d111672 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83675, d111672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d83675, d111672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h23 (q : Pattern) (ha : d83678 q = 1) (hb : d111675 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83678, d111675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20684 q ha hb
    | true =>
      simp only [d83678, d111675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d83679 q = 1) (hb : d111676 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83679, d111676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d83679, d111676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h28 (q : Pattern) (ha : d83680 q = 1) (hb : d111677 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83680, d111677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d83680, d111677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d83681 q = 1) (hb : d111678 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83681, d111678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d83681, d111678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d83682 q = 1) (hb : d111679 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83682, d111679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d83682, d111679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d83683 q = 1) (hb : d111680 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83683, d111680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d83683, d111680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro20686 (p : Pattern) (ha : d83690 p = 1) (hb : d111687 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83678 q = 1) (hb : d111675 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83678, d111675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20684 q ha hb
    | true =>
      simp only [d83678, d111675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d83679 q = 1) (hb : d111676 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83679, d111676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d83679, d111676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h6 (q : Pattern) (ha : d83680 q = 1) (hb : d111677 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83680, d111677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d83680, d111677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d83688 q = 1) (hb : d111685 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83688, d111685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83688, d111685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83689 q = 1) (hb : d111686 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83689, d111686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83689, d111686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d83690 q = 1) (hb : d111687 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83690, d111687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83690, d111687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro20687 (p : Pattern) (ha : d83703 p = 1) (hb : d111696 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d684 q = 1) (hb : d83698 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d684, d83698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14150 q ha hb
    | true =>
      simp only [d684, d83698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d685 q = 1) (hb : d83699 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d685, d83699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d685, d83699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d83700 q = 1) (hb : d111693 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83700, d111693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d83700, d111693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83701 q = 1) (hb : d111694 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83701, d111694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83701, d111694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d83702 q = 1) (hb : d111695 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83702, d111695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83702, d111695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d83703 q = 1) (hb : d111696 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83703, d111696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d83703, d111696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20688 (p : Pattern) (ha : d83709 p = 1) (hb : d111702 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83704 q = 1) (hb : d111697 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83704, d111697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20687 q ha hb
    | true =>
      simp only [d83704, d111697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51936 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d83705 q = 1) (hb : d111698 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83705, d111698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d83705, d111698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h6 (q : Pattern) (ha : d83706 q = 1) (hb : d111699 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83706, d111699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d83706, d111699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d83707 q = 1) (hb : d111700 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83707, d111700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83707, d111700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83708 q = 1) (hb : d111701 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83708, d111701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83708, d111701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d83709 q = 1) (hb : d111702 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83709, d111702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83709, d111702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro20689 (p : Pattern) (ha : d83715 p = 1) (hb : d111708 p = 1) : d0 p = 1 := by
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
  have h6 (q : Pattern) (ha : d83684 q = 1) (hb : d111681 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83684, d111681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20683 q ha hb
    | true =>
      simp only [d83684, d111681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20685 q ha hb
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
  have h8 (q : Pattern) (ha : d83685 q = 1) (hb : d111682 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83685, d111682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83685, d111682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d83686 q = 1) (hb : d111683 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83686, d111683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d83686, d111683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d83687 q = 1) (hb : d111684 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d83687, d111684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d83687, d111684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d83691 q = 1) (hb : d111688 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83691, d111688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83691, d111688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20686 q ha hb
  have h12 (q : Pattern) (ha : d83692 q = 1) (hb : d111689 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83692, d111689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d83692, d111689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d83693 q = 1) (hb : d111690 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83693, d111690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d83693, d111690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d83694 q = 1) (hb : d111691 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d83694, d111691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d83694, d111691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d83695 q = 1) (hb : d111692 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d83695, d111692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d83695, d111692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d83710 q = 1) (hb : d111703 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83710, d111703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83710, d111703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20688 q ha hb
  have h17 (q : Pattern) (ha : d83711 q = 1) (hb : d111704 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83711, d111704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d83711, d111704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d83712 q = 1) (hb : d111705 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83712, d111705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d83712, d111705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d83713 q = 1) (hb : d111706 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d83713, d111706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d83713, d111706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d83714 q = 1) (hb : d111707 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d83714, d111707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d83714, d111707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d83715 q = 1) (hb : d111708 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d83715, d111708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d83715, d111708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro20690 (p : Pattern) (ha : d83725 p = 1) (hb : d111718 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83671 q = 1) (hb : d111668 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83671, d111668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20682 q ha hb
    | true =>
      simp only [d83671, d111668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h2 (q : Pattern) (ha : d83721 q = 1) (hb : d111714 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83721, d111714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83721, d111714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83722 q = 1) (hb : d111715 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83722, d111715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83722, d111715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83723 q = 1) (hb : d111716 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83723, d111716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83723, d111716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83724 q = 1) (hb : d111717 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83724, d111717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83724, d111717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83725 q = 1) (hb : d111718 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83725, d111718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83725, d111718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20691 (p : Pattern) (ha : d83732 p = 1) (hb : d111725 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83671 q = 1) (hb : d111668 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83671, d111668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20682 q ha hb
    | true =>
      simp only [d83671, d111668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h2 (q : Pattern) (ha : d83721 q = 1) (hb : d111714 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83721, d111714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83721, d111714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83722 q = 1) (hb : d111715 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83722, d111715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83722, d111715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83723 q = 1) (hb : d111716 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83723, d111716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83723, d111716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83724 q = 1) (hb : d111717 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83724, d111717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83724, d111717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83678 q = 1) (hb : d111675 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83678, d111675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20684 q ha hb
    | true =>
      simp only [d83678, d111675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h7 (q : Pattern) (ha : d83728 q = 1) (hb : d111721 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83728, d111721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83728, d111721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83729 q = 1) (hb : d111722 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83729, d111722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d83729, d111722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d83730 q = 1) (hb : d111723 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83730, d111723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83730, d111723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d83731 q = 1) (hb : d111724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83731, d111724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83731, d111724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d83732 q = 1) (hb : d111725 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83732, d111725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83732, d111725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro20692 (p : Pattern) (ha : d491 p = 1) (hb : d83761 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d83665 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d83665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14142 q ha hb
    | true =>
      simp only [d482, d83665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d83666 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d83666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d83666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d83758 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d83758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d83758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d83759 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d83759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, d83759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d490 q = 1) (hb : d83760 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d490, d83760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d490, d83760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d491 q = 1) (hb : d83761 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d491, d83761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d491, d83761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20693 (p : Pattern) (ha : d83737 p = 1) (hb : d111730 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d83665 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d83665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14142 q ha hb
    | true =>
      simp only [d482, d83665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d83666 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d83666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d83666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d83667 q = 1) (hb : d111664 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83667, d111664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d83667, d111664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83668 q = 1) (hb : d111665 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83668, d111665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83668, d111665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d83736 q = 1) (hb : d111729 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83736, d111729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83736, d111729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83737 q = 1) (hb : d111730 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83737, d111730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83737, d111730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20694 (p : Pattern) (ha : d83744 p = 1) (hb : d111737 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d83665 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d83665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14142 q ha hb
    | true =>
      simp only [d482, d83665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d83666 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d83666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d83666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d83667 q = 1) (hb : d111664 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83667, d111664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d83667, d111664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83742 q = 1) (hb : d111735 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83742, d111735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83742, d111735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83743 q = 1) (hb : d111736 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83743, d111736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83743, d111736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d83744 q = 1) (hb : d111737 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83744, d111737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83744, d111737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20695 (p : Pattern) (ha : d83755 p = 1) (hb : d111744 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83750 q = 1) (hb : d98846 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83750, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14162 q ha hb
    | true =>
      simp only [d83750, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83751 q = 1) (hb : d98847 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83751, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83751, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d83665 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d83665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14142 q ha hb
    | true =>
      simp only [d482, d83665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d83666 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d83666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d83666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83752 q = 1) (hb : d111741 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83752, d111741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83752, d111741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83753 q = 1) (hb : d111742 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83753, d111742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83753, d111742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d83754 q = 1) (hb : d111743 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83754, d111743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83754, d111743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d83755 q = 1) (hb : d111744 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83755, d111744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83755, d111744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20696 (p : Pattern) (ha : d83767 p = 1) (hb : d111751 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83738 q = 1) (hb : d111731 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83738, d111731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20693 q ha hb
    | true =>
      simp only [d83738, d111731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q hb ha
  have h2 (q : Pattern) (ha : d83739 q = 1) (hb : d111732 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83739, d111732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83739, d111732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83740 q = 1) (hb : d111733 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83740, d111733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83740, d111733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83741 q = 1) (hb : d111734 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83741, d111734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83741, d111734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83745 q = 1) (hb : d111738 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83745, d111738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20694 q ha hb
    | true =>
      simp only [d83745, d111738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q hb ha
  have h6 (q : Pattern) (ha : d83746 q = 1) (hb : d111739 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83746, d111739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83746, d111739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83747 q = 1) (hb : d111740 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83747, d111740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83747, d111740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d83756 q = 1) (hb : d111745 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83756, d111745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20695 q ha hb
    | true =>
      simp only [d83756, d111745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20682 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d83671 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d83757 q = 1) (hb : d111746 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83757, d111746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d83757, d111746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d633 q = 1) (hb : d83762 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d633, d83762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20692 q ha hb
    | true =>
      simp only [d633, d83762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d83763 q = 1) (hb : d111747 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83763, d111747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d83763, d111747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d83764 q = 1) (hb : d111748 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83764, d111748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d83764, d111748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d83765 q = 1) (hb : d111749 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83765, d111749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d83765, d111749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d83766 q = 1) (hb : d111750 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83766, d111750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d83766, d111750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d83767 q = 1) (hb : d111751 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83767, d111751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83767, d111751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro20697 (p : Pattern) (ha : d501 p = 1) (hb : d83780 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d83665 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d83665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14142 q ha hb
    | true =>
      simp only [d482, d83665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d83666 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d83666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d83666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d83758 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d83758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d83758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d83759 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d83759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, d83759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d490 q = 1) (hb : d83760 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d490, d83760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d490, d83760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d501 q = 1) (hb : d83780 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d501, d83780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d501, d83780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro20698 (p : Pattern) (ha : d83768 p = 1) (hb : d111752 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d83665 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d83665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14142 q ha hb
    | true =>
      simp only [d482, d83665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d83666 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d83666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d83666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d83667 q = 1) (hb : d111664 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83667, d111664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d83667, d111664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83668 q = 1) (hb : d111665 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83668, d111665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83668, d111665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d83736 q = 1) (hb : d111729 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83736, d111729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83736, d111729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83768 q = 1) (hb : d111752 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83768, d111752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d83768, d111752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20699 (p : Pattern) (ha : d83773 p = 1) (hb : d111757 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d83665 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d83665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14142 q ha hb
    | true =>
      simp only [d482, d83665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d83666 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d83666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d83666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d83667 q = 1) (hb : d111664 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83667, d111664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d83667, d111664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83742 q = 1) (hb : d111735 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83742, d111735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83742, d111735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83743 q = 1) (hb : d111736 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83743, d111736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83743, d111736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d83773 q = 1) (hb : d111757 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83773, d111757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d83773, d111757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20700 (p : Pattern) (ha : d83777 p = 1) (hb : d111761 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83750 q = 1) (hb : d98846 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83750, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14162 q ha hb
    | true =>
      simp only [d83750, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83751 q = 1) (hb : d98847 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83751, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83751, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d83665 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d83665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14142 q ha hb
    | true =>
      simp only [d482, d83665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d83666 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d83666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d83666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83752 q = 1) (hb : d111741 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83752, d111741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83752, d111741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83753 q = 1) (hb : d111742 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83753, d111742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83753, d111742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d83754 q = 1) (hb : d111743 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83754, d111743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83754, d111743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d83777 q = 1) (hb : d111761 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83777, d111761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d83777, d111761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20701 (p : Pattern) (ha : d83786 p = 1) (hb : d111768 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83738 q = 1) (hb : d111731 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83738, d111731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20693 q ha hb
    | true =>
      simp only [d83738, d111731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q hb ha
  have h2 (q : Pattern) (ha : d83739 q = 1) (hb : d111732 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83739, d111732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83739, d111732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83740 q = 1) (hb : d111733 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83740, d111733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83740, d111733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83741 q = 1) (hb : d111734 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83741, d111734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83741, d111734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83745 q = 1) (hb : d111738 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83745, d111738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20694 q ha hb
    | true =>
      simp only [d83745, d111738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q hb ha
  have h6 (q : Pattern) (ha : d83746 q = 1) (hb : d111739 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83746, d111739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83746, d111739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83747 q = 1) (hb : d111740 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83747, d111740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83747, d111740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d83756 q = 1) (hb : d111745 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83756, d111745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20695 q ha hb
    | true =>
      simp only [d83756, d111745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20682 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d83671 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d83757 q = 1) (hb : d111746 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83757, d111746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d83757, d111746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d633 q = 1) (hb : d83762 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d633, d83762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20692 q ha hb
    | true =>
      simp only [d633, d83762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d83763 q = 1) (hb : d111747 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83763, d111747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d83763, d111747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d83764 q = 1) (hb : d111748 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83764, d111748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d83764, d111748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d83765 q = 1) (hb : d111749 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83765, d111749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d83765, d111749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d83766 q = 1) (hb : d111750 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83766, d111750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d83766, d111750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d83769 q = 1) (hb : d111753 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83769, d111753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20698 q ha hb
    | true =>
      simp only [d83769, d111753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32 q hb ha
  have h17 (q : Pattern) (ha : d83770 q = 1) (hb : d111754 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83770, d111754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83770, d111754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d83771 q = 1) (hb : d111755 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83771, d111755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d83771, d111755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d83772 q = 1) (hb : d111756 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83772, d111756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83772, d111756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d83774 q = 1) (hb : d111758 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83774, d111758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20699 q ha hb
    | true =>
      simp only [d83774, d111758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33 q hb ha
  have h21 (q : Pattern) (ha : d83775 q = 1) (hb : d111759 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83775, d111759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83775, d111759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d83776 q = 1) (hb : d111760 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83776, d111760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d83776, d111760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d83778 q = 1) (hb : d111762 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83778, d111762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20700 q ha hb
    | true =>
      simp only [d83778, d111762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20684 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d83678 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d83779 q = 1) (hb : d111763 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83779, d111763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d83779, d111763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d639 q = 1) (hb : d83781 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d639, d83781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20697 q ha hb
    | true =>
      simp only [d639, d83781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d83782 q = 1) (hb : d111764 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83782, d111764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q hb ha
    | true =>
      simp only [d83782, d111764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d83783 q = 1) (hb : d111765 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83783, d111765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d83783, d111765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d83784 q = 1) (hb : d111766 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83784, d111766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d83784, d111766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d83785 q = 1) (hb : d111767 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83785, d111767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d83785, d111767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d83786 q = 1) (hb : d111768 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83786, d111768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d83786, d111768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro20702 (p : Pattern) (ha : d83788 p = 1) (hb : d111770 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83671 q = 1) (hb : d111668 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83671, d111668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20682 q ha hb
    | true =>
      simp only [d83671, d111668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h2 (q : Pattern) (ha : d83721 q = 1) (hb : d111714 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83721, d111714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83721, d111714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83722 q = 1) (hb : d111715 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83722, d111715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83722, d111715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83723 q = 1) (hb : d111716 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83723, d111716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83723, d111716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83724 q = 1) (hb : d111717 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83724, d111717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83724, d111717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h11 (q : Pattern) (ha : d83788 q = 1) (hb : d111770 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83788, d111770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83788, d111770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro20703 (p : Pattern) (ha : d83795 p = 1) (hb : d111777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83778 q = 1) (hb : d111762 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83778, d111762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20700 q ha hb
    | true =>
      simp only [d83778, d111762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20684 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d83678 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d83779 q = 1) (hb : d111763 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83779, d111763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d83779, d111763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d639 q = 1) (hb : d83781 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d639, d83781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20697 q ha hb
    | true =>
      simp only [d639, d83781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d83782 q = 1) (hb : d111764 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83782, d111764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d83782, d111764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d83783 q = 1) (hb : d111765 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83783, d111765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d83783, d111765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83793 q = 1) (hb : d111775 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83793, d111775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83793, d111775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83794 q = 1) (hb : d111776 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83794, d111776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83794, d111776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d83795 q = 1) (hb : d111777 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83795, d111777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83795, d111777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro20704 (p : Pattern) (ha : d730 p = 1) (hb : d83814 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d684 q = 1) (hb : d83698 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d684, d83698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14150 q ha hb
    | true =>
      simp only [d684, d83698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d685 q = 1) (hb : d83699 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d685, d83699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d685, d83699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d727 q = 1) (hb : d83811 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d727, d83811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d727, d83811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d728 q = 1) (hb : d83812 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d728, d83812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d728, d83812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d729 q = 1) (hb : d83813 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d729, d83813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d729, d83813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d730 q = 1) (hb : d83814 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d730, d83814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d730, d83814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro20705 (p : Pattern) (ha : d83808 p = 1) (hb : d111786 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83803 q = 1) (hb : d98879 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83803, d98879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14171 q ha hb
    | true =>
      simp only [d83803, d98879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83804 q = 1) (hb : d98880 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83804, d98880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83804, d98880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d684 q = 1) (hb : d83698 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d684, d83698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14150 q ha hb
    | true =>
      simp only [d684, d83698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d685 q = 1) (hb : d83699 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d685, d83699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d685, d83699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83805 q = 1) (hb : d111783 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83805, d111783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83805, d111783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83806 q = 1) (hb : d111784 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83806, d111784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83806, d111784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d83807 q = 1) (hb : d111785 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83807, d111785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83807, d111785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d83808 q = 1) (hb : d111786 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83808, d111786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d83808, d111786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20706 (p : Pattern) (ha : d83820 p = 1) (hb : d111793 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83809 q = 1) (hb : d111787 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83809, d111787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20705 q ha hb
    | true =>
      simp only [d83809, d111787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20687 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d83704 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d83810 q = 1) (hb : d111788 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83810, d111788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d83810, d111788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d731 q = 1) (hb : d83815 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d731, d83815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20704 q ha hb
    | true =>
      simp only [d731, d83815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d83816 q = 1) (hb : d111789 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83816, d111789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d83816, d111789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d83817 q = 1) (hb : d111790 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83817, d111790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d83817, d111790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83818 q = 1) (hb : d111791 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83818, d111791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83818, d111791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83819 q = 1) (hb : d111792 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83819, d111792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83819, d111792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d83820 q = 1) (hb : d111793 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83820, d111793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83820, d111793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro20707 (p : Pattern) (ha : d83826 p = 1) (hb : d111799 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83726 q = 1) (hb : d111719 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83726, d111719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83726, d111719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20690 q ha hb
  have h2 (q : Pattern) (ha : d83727 q = 1) (hb : d111720 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83727, d111720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d83727, d111720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d83733 q = 1) (hb : d111726 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83733, d111726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20690 q ha hb
    | true =>
      simp only [d83733, d111726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20691 q ha hb
  have h4 (q : Pattern) (ha : d83734 q = 1) (hb : d111727 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83734, d111727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d83734, d111727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d83735 q = 1) (hb : d111728 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83735, d111728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83735, d111728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83787 q = 1) (hb : d111769 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83787, d111769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20696 q ha hb
    | true =>
      simp only [d83787, d111769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20701 q ha hb
  have h7 (q : Pattern) (ha : d83789 q = 1) (hb : d111771 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83789, d111771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20702 q ha hb
    | true =>
      simp only [d83789, d111771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16 q hb ha
  have h8 (q : Pattern) (ha : d83790 q = 1) (hb : d111772 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83790, d111772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83790, d111772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d83791 q = 1) (hb : d111773 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83791, d111773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d83791, d111773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d83792 q = 1) (hb : d111774 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d83792, d111774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83792, d111774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d83796 q = 1) (hb : d111778 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83796, d111778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83796, d111778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20703 q ha hb
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
  have h13 (q : Pattern) (ha : d83797 q = 1) (hb : d111779 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83797, d111779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d83797, d111779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d83798 q = 1) (hb : d111780 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83798, d111780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d83798, d111780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d83799 q = 1) (hb : d111781 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d83799, d111781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d83799, d111781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d83800 q = 1) (hb : d111782 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d83800, d111782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d83800, d111782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d83821 q = 1) (hb : d111794 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83821, d111794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83821, d111794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20706 q ha hb
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
  have h19 (q : Pattern) (ha : d83822 q = 1) (hb : d111795 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83822, d111795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d83822, d111795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d83823 q = 1) (hb : d111796 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83823, d111796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d83823, d111796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d83824 q = 1) (hb : d111797 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d83824, d111797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d83824, d111797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d83825 q = 1) (hb : d111798 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d83825, d111798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d83825, d111798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d83826 q = 1) (hb : d111799 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d83826, d111799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d83826, d111799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro20708 (p : Pattern) (ha : d83832 p = 1) (hb : d111805 p = 1) : d0 p = 1 := by
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
  have h5 (q : Pattern) (ha : d83716 q = 1) (hb : d111709 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d83716, d111709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83716, d111709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20689 q ha hb
  have h6 (q : Pattern) (ha : d83717 q = 1) (hb : d111710 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d83717, d111710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83717, d111710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83718 q = 1) (hb : d111711 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d83718, d111711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83718, d111711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83719 q = 1) (hb : d111712 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d83719, d111712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83719, d111712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d83720 q = 1) (hb : d111713 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d83720, d111713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d83720, d111713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d83827 q = 1) (hb : d111800 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d83827, d111800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83827, d111800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20707 q ha hb
  have h11 (q : Pattern) (ha : d83828 q = 1) (hb : d111801 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d83828, d111801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83828, d111801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d83829 q = 1) (hb : d111802 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d83829, d111802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83829, d111802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d83830 q = 1) (hb : d111803 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d83830, d111803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83830, d111803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d83831 q = 1) (hb : d111804 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d83831, d111804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83831, d111804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d83832 q = 1) (hb : d111805 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d83832, d111805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d83832, d111805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro20709 (p : Pattern) (ha : d83836 p = 1) (hb : d111744 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83750 q = 1) (hb : d98846 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83750, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14162 q ha hb
    | true =>
      simp only [d83750, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83751 q = 1) (hb : d98847 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83751, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83751, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d52229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61 q ha hb
    | true =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83833 q = 1) (hb : d111741 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83833, d111741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83833, d111741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83834 q = 1) (hb : d111742 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83834, d111742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83834, d111742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d83835 q = 1) (hb : d111743 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83835, d111743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83835, d111743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d83836 q = 1) (hb : d111744 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83836, d111744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83836, d111744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20710 (p : Pattern) (ha : d83842 p = 1) (hb : d111811 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83837 q = 1) (hb : d111806 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83837, d111806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20709 q ha hb
    | true =>
      simp only [d83837, d111806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63 q hb ha
  have h2 (q : Pattern) (ha : d83838 q = 1) (hb : d111807 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83838, d111807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83838, d111807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83839 q = 1) (hb : d111808 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83839, d111808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83839, d111808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83840 q = 1) (hb : d111809 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83840, d111809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83840, d111809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83841 q = 1) (hb : d111810 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83841, d111810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83841, d111810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83842 q = 1) (hb : d111811 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83842, d111811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83842, d111811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20711 (p : Pattern) (ha : d83845 p = 1) (hb : d111761 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83750 q = 1) (hb : d98846 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83750, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14162 q ha hb
    | true =>
      simp only [d83750, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83751 q = 1) (hb : d98847 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83751, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83751, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d52229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61 q ha hb
    | true =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83833 q = 1) (hb : d111741 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83833, d111741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83833, d111741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83834 q = 1) (hb : d111742 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83834, d111742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83834, d111742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d83835 q = 1) (hb : d111743 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83835, d111743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83835, d111743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d83845 q = 1) (hb : d111761 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83845, d111761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d83845, d111761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20712 (p : Pattern) (ha : d83851 p = 1) (hb : d111819 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83837 q = 1) (hb : d111806 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83837, d111806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20709 q ha hb
    | true =>
      simp only [d83837, d111806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63 q hb ha
  have h2 (q : Pattern) (ha : d83838 q = 1) (hb : d111807 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83838, d111807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83838, d111807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83839 q = 1) (hb : d111808 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83839, d111808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83839, d111808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83840 q = 1) (hb : d111809 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83840, d111809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83840, d111809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83841 q = 1) (hb : d111810 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83841, d111810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83841, d111810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83846 q = 1) (hb : d111814 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83846, d111814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20711 q ha hb
    | true =>
      simp only [d83846, d111814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66 q hb ha
  have h7 (q : Pattern) (ha : d83847 q = 1) (hb : d111815 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83847, d111815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83847, d111815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83848 q = 1) (hb : d111816 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83848, d111816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d83848, d111816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d83849 q = 1) (hb : d111817 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83849, d111817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83849, d111817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d83850 q = 1) (hb : d111818 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83850, d111818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83850, d111818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d83851 q = 1) (hb : d111819 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83851, d111819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83851, d111819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro20713 (p : Pattern) (ha : d83856 p = 1) (hb : d111824 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83750 q = 1) (hb : d98846 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83750, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14162 q ha hb
    | true =>
      simp only [d83750, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83751 q = 1) (hb : d98847 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83751, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83751, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d52229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61 q ha hb
    | true =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83833 q = 1) (hb : d111741 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83833, d111741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83833, d111741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83834 q = 1) (hb : d111742 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83834, d111742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83834, d111742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d83855 q = 1) (hb : d111823 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83855, d111823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83855, d111823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83856 q = 1) (hb : d111824 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83856, d111824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83856, d111824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20714 (p : Pattern) (ha : d83863 p = 1) (hb : d111831 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83750 q = 1) (hb : d98846 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83750, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14162 q ha hb
    | true =>
      simp only [d83750, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83751 q = 1) (hb : d98847 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83751, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83751, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d52229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61 q ha hb
    | true =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83833 q = 1) (hb : d111741 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83833, d111741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83833, d111741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83861 q = 1) (hb : d111829 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83861, d111829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83861, d111829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83862 q = 1) (hb : d111830 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83862, d111830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83862, d111830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d83863 q = 1) (hb : d111831 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83863, d111831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83863, d111831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20715 (p : Pattern) (ha : d83868 p = 1) (hb : d111836 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d549 q = 1) (hb : d52296 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d549, d52296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77 q ha hb
    | true =>
      simp only [d549, d52296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43 q ha hb
  have h2 (q : Pattern) (ha : d550 q = 1) (hb : d52297 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d550, d52297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d550, d52297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d551 q = 1) (hb : d52298 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d551, d52298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d551, d52298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52126 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d8451 q = 1) (hb : d52299 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d8451, d52299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8451, d52299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83867 q = 1) (hb : d111835 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d83867, d111835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d83867, d111835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d83868 q = 1) (hb : d111836 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d83868, d111836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83868, d111836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro20716 (p : Pattern) (ha : d83874 p = 1) (hb : d111842 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83869 q = 1) (hb : d111837 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83869, d111837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20715 q ha hb
    | true =>
      simp only [d83869, d111837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83870 q = 1) (hb : d111838 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83870, d111838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83870, d111838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83750 q = 1) (hb : d98846 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83750, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14162 q ha hb
    | true =>
      simp only [d83750, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83751 q = 1) (hb : d98847 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83751, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83751, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83871 q = 1) (hb : d111839 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83871, d111839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83871, d111839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83872 q = 1) (hb : d111840 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83872, d111840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83872, d111840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d83873 q = 1) (hb : d111841 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83873, d111841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83873, d111841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d83874 q = 1) (hb : d111842 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83874, d111842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83874, d111842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20717 (p : Pattern) (ha : d83880 p = 1) (hb : d111848 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83750 q = 1) (hb : d98846 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83750, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14162 q ha hb
    | true =>
      simp only [d83750, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83751 q = 1) (hb : d98847 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83751, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83751, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83877 q = 1) (hb : d111845 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83877, d111845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83877, d111845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83878 q = 1) (hb : d111846 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83878, d111846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d83878, d111846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d83879 q = 1) (hb : d111847 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83879, d111847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d83879, d111847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d83880 q = 1) (hb : d111848 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83880, d111848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83880, d111848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20718 (p : Pattern) (ha : d83886 p = 1) (hb : d111854 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83857 q = 1) (hb : d111825 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83857, d111825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20713 q ha hb
    | true =>
      simp only [d83857, d111825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88 q hb ha
  have h2 (q : Pattern) (ha : d83858 q = 1) (hb : d111826 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83858, d111826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83858, d111826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83859 q = 1) (hb : d111827 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83859, d111827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83859, d111827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83860 q = 1) (hb : d111828 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83860, d111828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83860, d111828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83864 q = 1) (hb : d111832 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83864, d111832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20714 q ha hb
    | true =>
      simp only [d83864, d111832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90 q hb ha
  have h6 (q : Pattern) (ha : d83865 q = 1) (hb : d111833 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83865, d111833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83865, d111833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83866 q = 1) (hb : d111834 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83866, d111834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83866, d111834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d83875 q = 1) (hb : d111843 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83875, d111843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20716 q ha hb
    | true =>
      simp only [d83875, d111843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20709 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d83837 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d83876 q = 1) (hb : d111844 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83876, d111844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d83876, d111844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d83881 q = 1) (hb : d111849 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83881, d111849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20717 q ha hb
    | true =>
      simp only [d83881, d111849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d83882 q = 1) (hb : d111850 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83882, d111850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d83882, d111850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d83883 q = 1) (hb : d111851 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83883, d111851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d83883, d111851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d83884 q = 1) (hb : d111852 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83884, d111852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d83884, d111852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d83885 q = 1) (hb : d111853 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83885, d111853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d83885, d111853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d83886 q = 1) (hb : d111854 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83886, d111854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83886, d111854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro20719 (p : Pattern) (ha : d83887 p = 1) (hb : d111855 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83750 q = 1) (hb : d98846 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83750, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14162 q ha hb
    | true =>
      simp only [d83750, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83751 q = 1) (hb : d98847 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83751, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83751, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d52229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61 q ha hb
    | true =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83833 q = 1) (hb : d111741 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83833, d111741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83833, d111741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83834 q = 1) (hb : d111742 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83834, d111742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83834, d111742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d83855 q = 1) (hb : d111823 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83855, d111823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83855, d111823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83887 q = 1) (hb : d111855 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83887, d111855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d83887, d111855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20720 (p : Pattern) (ha : d83892 p = 1) (hb : d111860 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83750 q = 1) (hb : d98846 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83750, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14162 q ha hb
    | true =>
      simp only [d83750, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83751 q = 1) (hb : d98847 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83751, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83751, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d52229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61 q ha hb
    | true =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83833 q = 1) (hb : d111741 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83833, d111741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83833, d111741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83861 q = 1) (hb : d111829 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83861, d111829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83861, d111829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83862 q = 1) (hb : d111830 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83862, d111830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83862, d111830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d83892 q = 1) (hb : d111860 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83892, d111860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d83892, d111860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20721 (p : Pattern) (ha : d83896 p = 1) (hb : d111864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83869 q = 1) (hb : d111837 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83869, d111837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20715 q ha hb
    | true =>
      simp only [d83869, d111837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83870 q = 1) (hb : d111838 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83870, d111838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83870, d111838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83750 q = 1) (hb : d98846 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83750, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14162 q ha hb
    | true =>
      simp only [d83750, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83751 q = 1) (hb : d98847 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83751, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83751, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83871 q = 1) (hb : d111839 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83871, d111839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83871, d111839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83872 q = 1) (hb : d111840 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83872, d111840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83872, d111840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d83873 q = 1) (hb : d111841 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83873, d111841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83873, d111841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d83896 q = 1) (hb : d111864 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83896, d111864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d83896, d111864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20722 (p : Pattern) (ha : d83899 p = 1) (hb : d111867 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83750 q = 1) (hb : d98846 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83750, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14162 q ha hb
    | true =>
      simp only [d83750, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83751 q = 1) (hb : d98847 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83751, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83751, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83877 q = 1) (hb : d111845 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83877, d111845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83877, d111845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83878 q = 1) (hb : d111846 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83878, d111846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d83878, d111846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d83879 q = 1) (hb : d111847 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83879, d111847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d83879, d111847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d83899 q = 1) (hb : d111867 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83899, d111867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83899, d111867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20723 (p : Pattern) (ha : d83905 p = 1) (hb : d111873 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83857 q = 1) (hb : d111825 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83857, d111825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20713 q ha hb
    | true =>
      simp only [d83857, d111825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88 q hb ha
  have h2 (q : Pattern) (ha : d83858 q = 1) (hb : d111826 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83858, d111826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83858, d111826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83859 q = 1) (hb : d111827 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83859, d111827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83859, d111827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83860 q = 1) (hb : d111828 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83860, d111828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83860, d111828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83864 q = 1) (hb : d111832 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83864, d111832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20714 q ha hb
    | true =>
      simp only [d83864, d111832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90 q hb ha
  have h6 (q : Pattern) (ha : d83865 q = 1) (hb : d111833 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83865, d111833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83865, d111833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83866 q = 1) (hb : d111834 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83866, d111834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83866, d111834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d83875 q = 1) (hb : d111843 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83875, d111843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20716 q ha hb
    | true =>
      simp only [d83875, d111843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20709 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d83837 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d83876 q = 1) (hb : d111844 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83876, d111844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d83876, d111844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d83881 q = 1) (hb : d111849 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83881, d111849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20717 q ha hb
    | true =>
      simp only [d83881, d111849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d83882 q = 1) (hb : d111850 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83882, d111850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d83882, d111850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d83883 q = 1) (hb : d111851 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83883, d111851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d83883, d111851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d83884 q = 1) (hb : d111852 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83884, d111852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d83884, d111852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d83885 q = 1) (hb : d111853 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83885, d111853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d83885, d111853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d83888 q = 1) (hb : d111856 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83888, d111856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20719 q ha hb
    | true =>
      simp only [d83888, d111856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94 q hb ha
  have h17 (q : Pattern) (ha : d83889 q = 1) (hb : d111857 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83889, d111857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83889, d111857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d83890 q = 1) (hb : d111858 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83890, d111858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d83890, d111858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d83891 q = 1) (hb : d111859 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83891, d111859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83891, d111859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d83893 q = 1) (hb : d111861 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83893, d111861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20720 q ha hb
    | true =>
      simp only [d83893, d111861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96 q hb ha
  have h21 (q : Pattern) (ha : d83894 q = 1) (hb : d111862 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83894, d111862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83894, d111862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d83895 q = 1) (hb : d111863 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83895, d111863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d83895, d111863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d83897 q = 1) (hb : d111865 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83897, d111865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20721 q ha hb
    | true =>
      simp only [d83897, d111865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20711 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d83846 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d83898 q = 1) (hb : d111866 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83898, d111866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d83898, d111866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d83900 q = 1) (hb : d111868 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83900, d111868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20722 q ha hb
    | true =>
      simp only [d83900, d111868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d83901 q = 1) (hb : d111869 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83901, d111869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d83901, d111869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d83902 q = 1) (hb : d111870 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83902, d111870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d83902, d111870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d83903 q = 1) (hb : d111871 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83903, d111871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d83903, d111871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d83904 q = 1) (hb : d111872 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83904, d111872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d83904, d111872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d83905 q = 1) (hb : d111873 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83905, d111873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d83905, d111873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro20724 (p : Pattern) (ha : d83907 p = 1) (hb : d111875 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83837 q = 1) (hb : d111806 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83837, d111806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20709 q ha hb
    | true =>
      simp only [d83837, d111806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63 q hb ha
  have h2 (q : Pattern) (ha : d83838 q = 1) (hb : d111807 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83838, d111807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83838, d111807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83839 q = 1) (hb : d111808 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83839, d111808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83839, d111808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83840 q = 1) (hb : d111809 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83840, d111809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83840, d111809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83841 q = 1) (hb : d111810 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83841, d111810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83841, d111810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d633 q = 1) (hb : d52337 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d633, d52337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63 q ha hb
    | true =>
      simp only [d633, d52337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d634 q = 1) (hb : d52338 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d634, d52338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d634, d52338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d635 q = 1) (hb : d52339 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d635, d52339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d635, d52339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d636 q = 1) (hb : d52340 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d636, d52340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d636, d52340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d637 q = 1) (hb : d52341 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d637, d52341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d637, d52341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d83907 q = 1) (hb : d111875 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83907, d111875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83907, d111875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro20725 (p : Pattern) (ha : d83914 p = 1) (hb : d111882 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83897 q = 1) (hb : d111865 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83897, d111865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20721 q ha hb
    | true =>
      simp only [d83897, d111865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20711 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d83846 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d83898 q = 1) (hb : d111866 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83898, d111866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d83898, d111866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d83900 q = 1) (hb : d111868 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83900, d111868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20722 q ha hb
    | true =>
      simp only [d83900, d111868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d83901 q = 1) (hb : d111869 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83901, d111869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d83901, d111869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d83902 q = 1) (hb : d111870 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83902, d111870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d83902, d111870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83912 q = 1) (hb : d111880 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83912, d111880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83912, d111880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83913 q = 1) (hb : d111881 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83913, d111881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83913, d111881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d83914 q = 1) (hb : d111882 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83914, d111882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83914, d111882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro20726 (p : Pattern) (ha : d83921 p = 1) (hb : d111889 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d665 q = 1) (hb : d52369 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d665, d52369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81 q ha hb
    | true =>
      simp only [d665, d52369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47 q ha hb
  have h2 (q : Pattern) (ha : d666 q = 1) (hb : d52370 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d666, d52370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d666, d52370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d667 q = 1) (hb : d52371 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d667, d52371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d667, d52371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52186 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d8527 q = 1) (hb : d52372 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d8527, d52372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8527, d52372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83920 q = 1) (hb : d111888 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d83920, d111888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d83920, d111888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d83921 q = 1) (hb : d111889 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d83921, d111889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83921, d111889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro20727 (p : Pattern) (ha : d83927 p = 1) (hb : d111895 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83922 q = 1) (hb : d111890 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83922, d111890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20726 q ha hb
    | true =>
      simp only [d83922, d111890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83923 q = 1) (hb : d111891 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83923, d111891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83923, d111891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83803 q = 1) (hb : d98879 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83803, d98879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14171 q ha hb
    | true =>
      simp only [d83803, d98879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83804 q = 1) (hb : d98880 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83804, d98880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83804, d98880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83924 q = 1) (hb : d111892 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83924, d111892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83924, d111892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83925 q = 1) (hb : d111893 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83925, d111893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83925, d111893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d83926 q = 1) (hb : d111894 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83926, d111894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83926, d111894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d83927 q = 1) (hb : d111895 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83927, d111895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d83927, d111895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20728 (p : Pattern) (ha : d83931 p = 1) (hb : d111786 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83803 q = 1) (hb : d98879 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83803, d98879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14171 q ha hb
    | true =>
      simp only [d83803, d98879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83804 q = 1) (hb : d98880 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83804, d98880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83804, d98880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d684 q = 1) (hb : d52388 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d684, d52388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro71 q ha hb
    | true =>
      simp only [d684, d52388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d685 q = 1) (hb : d52389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d685, d52389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d685, d52389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83928 q = 1) (hb : d111783 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83928, d111783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83928, d111783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83929 q = 1) (hb : d111784 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83929, d111784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83929, d111784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d83930 q = 1) (hb : d111785 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83930, d111785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83930, d111785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d83931 q = 1) (hb : d111786 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83931, d111786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d83931, d111786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20729 (p : Pattern) (ha : d83938 p = 1) (hb : d111901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83803 q = 1) (hb : d98879 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83803, d98879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14171 q ha hb
    | true =>
      simp only [d83803, d98879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83804 q = 1) (hb : d98880 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83804, d98880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83804, d98880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83935 q = 1) (hb : d111898 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83935, d111898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83935, d111898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83936 q = 1) (hb : d111899 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83936, d111899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d83936, d111899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d83937 q = 1) (hb : d111900 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83937, d111900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d83937, d111900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d83938 q = 1) (hb : d111901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83938, d111901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83938, d111901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20730 (p : Pattern) (ha : d83944 p = 1) (hb : d111907 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83932 q = 1) (hb : d111896 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83932, d111896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20727 q ha hb
    | true =>
      simp only [d83932, d111896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20728 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d83933 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d83934 q = 1) (hb : d111897 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83934, d111897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d83934, d111897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d83939 q = 1) (hb : d111902 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83939, d111902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20729 q ha hb
    | true =>
      simp only [d83939, d111902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d83940 q = 1) (hb : d111903 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83940, d111903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d83940, d111903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d83941 q = 1) (hb : d111904 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83941, d111904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d83941, d111904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83942 q = 1) (hb : d111905 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83942, d111905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83942, d111905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83943 q = 1) (hb : d111906 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83943, d111906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83943, d111906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d83944 q = 1) (hb : d111907 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83944, d111907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83944, d111907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro20731 (p : Pattern) (ha : d83950 p = 1) (hb : d111913 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83843 q = 1) (hb : d111812 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83843, d111812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83843, d111812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20710 q ha hb
  have h2 (q : Pattern) (ha : d83844 q = 1) (hb : d111813 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83844, d111813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d83844, d111813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d83852 q = 1) (hb : d111820 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83852, d111820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20710 q ha hb
    | true =>
      simp only [d83852, d111820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20712 q ha hb
  have h4 (q : Pattern) (ha : d83853 q = 1) (hb : d111821 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83853, d111821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d83853, d111821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d83854 q = 1) (hb : d111822 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83854, d111822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83854, d111822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83906 q = 1) (hb : d111874 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83906, d111874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20718 q ha hb
    | true =>
      simp only [d83906, d111874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20723 q ha hb
  have h7 (q : Pattern) (ha : d83908 q = 1) (hb : d111876 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83908, d111876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20724 q ha hb
    | true =>
      simp only [d83908, d111876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69 q hb ha
  have h8 (q : Pattern) (ha : d83909 q = 1) (hb : d111877 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83909, d111877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83909, d111877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d83910 q = 1) (hb : d111878 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83910, d111878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d83910, d111878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d83911 q = 1) (hb : d111879 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d83911, d111879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83911, d111879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d83915 q = 1) (hb : d111883 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83915, d111883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83915, d111883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20725 q ha hb
  have h12 (q : Pattern) (ha : d654 q = 1) (hb : d52358 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d654, d52358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d654, d52358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70 q ha hb
  have h13 (q : Pattern) (ha : d83916 q = 1) (hb : d111884 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83916, d111884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d83916, d111884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d83917 q = 1) (hb : d111885 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83917, d111885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d83917, d111885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d83918 q = 1) (hb : d111886 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d83918, d111886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d83918, d111886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d83919 q = 1) (hb : d111887 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d83919, d111887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d83919, d111887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d83945 q = 1) (hb : d111908 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83945, d111908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83945, d111908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20730 q ha hb
  have h18 (q : Pattern) (ha : d737 q = 1) (hb : d52414 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d737, d52414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d737, d52414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73 q ha hb
  have h19 (q : Pattern) (ha : d83946 q = 1) (hb : d111909 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83946, d111909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d83946, d111909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d83947 q = 1) (hb : d111910 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83947, d111910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d83947, d111910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d83948 q = 1) (hb : d111911 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d83948, d111911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d83948, d111911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d83949 q = 1) (hb : d111912 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d83949, d111912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d83949, d111912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d83950 q = 1) (hb : d111913 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d83950, d111913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d83950, d111913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro20732 (p : Pattern) (ha : d83956 p = 1) (hb : d111919 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83951 q = 1) (hb : d111914 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d83951, d111914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83951, d111914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20731 q ha hb
  have h2 (q : Pattern) (ha : d83952 q = 1) (hb : d111915 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d83952, d111915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83952, d111915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83953 q = 1) (hb : d111916 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d83953, d111916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83953, d111916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d83954 q = 1) (hb : d111917 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d83954, d111917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83954, d111917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83955 q = 1) (hb : d111918 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d83955, d111918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83955, d111918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83956 q = 1) (hb : d111919 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d83956, d111919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83956, d111919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20733 (p : Pattern) (ha : d83965 p = 1) (hb : d111924 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83960 q = 1) (hb : d98906 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83960, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14183 q ha hb
    | true =>
      simp only [d83960, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83961 q = 1) (hb : d98907 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83961, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83961, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d52451 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105 q ha hb
    | true =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83962 q = 1) (hb : d111921 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83962, d111921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83962, d111921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83963 q = 1) (hb : d111922 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83963, d111922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83963, d111922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d83964 q = 1) (hb : d111923 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83964, d111923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83964, d111923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d83965 q = 1) (hb : d111924 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83965, d111924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83965, d111924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20734 (p : Pattern) (ha : d83971 p = 1) (hb : d111930 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83966 q = 1) (hb : d111925 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83966, d111925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20733 q ha hb
    | true =>
      simp only [d83966, d111925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107 q hb ha
  have h2 (q : Pattern) (ha : d83967 q = 1) (hb : d111926 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83967, d111926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83967, d111926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83968 q = 1) (hb : d111927 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83968, d111927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83968, d111927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83969 q = 1) (hb : d111928 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83969, d111928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83969, d111928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83970 q = 1) (hb : d111929 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83970, d111929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83970, d111929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83971 q = 1) (hb : d111930 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83971, d111930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83971, d111930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20735 (p : Pattern) (ha : d83974 p = 1) (hb : d111933 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83960 q = 1) (hb : d98906 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83960, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14183 q ha hb
    | true =>
      simp only [d83960, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83961 q = 1) (hb : d98907 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83961, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83961, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d52451 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105 q ha hb
    | true =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83962 q = 1) (hb : d111921 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83962, d111921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83962, d111921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83963 q = 1) (hb : d111922 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83963, d111922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83963, d111922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d83964 q = 1) (hb : d111923 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83964, d111923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83964, d111923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d83974 q = 1) (hb : d111933 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83974, d111933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d83974, d111933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20736 (p : Pattern) (ha : d83980 p = 1) (hb : d111939 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83966 q = 1) (hb : d111925 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83966, d111925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20733 q ha hb
    | true =>
      simp only [d83966, d111925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107 q hb ha
  have h2 (q : Pattern) (ha : d83967 q = 1) (hb : d111926 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83967, d111926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83967, d111926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83968 q = 1) (hb : d111927 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83968, d111927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83968, d111927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83969 q = 1) (hb : d111928 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83969, d111928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83969, d111928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83970 q = 1) (hb : d111929 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83970, d111929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83970, d111929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83975 q = 1) (hb : d111934 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83975, d111934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20735 q ha hb
    | true =>
      simp only [d83975, d111934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro110 q hb ha
  have h7 (q : Pattern) (ha : d83976 q = 1) (hb : d111935 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83976, d111935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83976, d111935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83977 q = 1) (hb : d111936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83977, d111936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d83977, d111936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d83978 q = 1) (hb : d111937 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83978, d111937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83978, d111937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d83979 q = 1) (hb : d111938 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83979, d111938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83979, d111938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d83980 q = 1) (hb : d111939 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83980, d111939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83980, d111939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro20737 (p : Pattern) (ha : d83985 p = 1) (hb : d111944 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83960 q = 1) (hb : d98906 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83960, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14183 q ha hb
    | true =>
      simp only [d83960, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83961 q = 1) (hb : d98907 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83961, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83961, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d52451 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105 q ha hb
    | true =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83962 q = 1) (hb : d111921 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83962, d111921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83962, d111921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83963 q = 1) (hb : d111922 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83963, d111922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83963, d111922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d83984 q = 1) (hb : d111943 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83984, d111943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83984, d111943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83985 q = 1) (hb : d111944 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83985, d111944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83985, d111944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20738 (p : Pattern) (ha : d83992 p = 1) (hb : d111951 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83960 q = 1) (hb : d98906 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83960, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14183 q ha hb
    | true =>
      simp only [d83960, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83961 q = 1) (hb : d98907 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83961, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83961, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d52451 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105 q ha hb
    | true =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83962 q = 1) (hb : d111921 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83962, d111921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83962, d111921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83990 q = 1) (hb : d111949 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83990, d111949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83990, d111949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83991 q = 1) (hb : d111950 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83991, d111950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83991, d111950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d83992 q = 1) (hb : d111951 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83992, d111951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83992, d111951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20739 (p : Pattern) (ha : d83997 p = 1) (hb : d111956 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d840 q = 1) (hb : d52517 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d840, d52517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro123 q ha hb
    | true =>
      simp only [d840, d52517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101 q ha hb
  have h2 (q : Pattern) (ha : d841 q = 1) (hb : d52518 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d841, d52518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d841, d52518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d842 q = 1) (hb : d52519 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d842, d52519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d842, d52519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52438 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d8613 q = 1) (hb : d52520 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d8613, d52520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8613, d52520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83996 q = 1) (hb : d111955 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d83996, d111955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d83996, d111955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d83997 q = 1) (hb : d111956 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d83997, d111956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83997, d111956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro20740 (p : Pattern) (ha : d84003 p = 1) (hb : d111962 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83998 q = 1) (hb : d111957 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83998, d111957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20739 q ha hb
    | true =>
      simp only [d83998, d111957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83999 q = 1) (hb : d111958 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83999, d111958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83999, d111958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83960 q = 1) (hb : d98906 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83960, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14183 q ha hb
    | true =>
      simp only [d83960, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83961 q = 1) (hb : d98907 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83961, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83961, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84000 q = 1) (hb : d111959 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84000, d111959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84000, d111959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84001 q = 1) (hb : d111960 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84001, d111960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84001, d111960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84002 q = 1) (hb : d111961 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84002, d111961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84002, d111961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84003 q = 1) (hb : d111962 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84003, d111962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84003, d111962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20741 (p : Pattern) (ha : d84009 p = 1) (hb : d111968 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83960 q = 1) (hb : d98906 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83960, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14183 q ha hb
    | true =>
      simp only [d83960, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83961 q = 1) (hb : d98907 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83961, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83961, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84006 q = 1) (hb : d111965 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84006, d111965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84006, d111965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84007 q = 1) (hb : d111966 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84007, d111966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84007, d111966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84008 q = 1) (hb : d111967 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84008, d111967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84008, d111967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84009 q = 1) (hb : d111968 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84009, d111968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84009, d111968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20742 (p : Pattern) (ha : d84015 p = 1) (hb : d111974 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83986 q = 1) (hb : d111945 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83986, d111945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20737 q ha hb
    | true =>
      simp only [d83986, d111945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro135 q hb ha
  have h2 (q : Pattern) (ha : d83987 q = 1) (hb : d111946 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83987, d111946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83987, d111946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83988 q = 1) (hb : d111947 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83988, d111947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83988, d111947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83989 q = 1) (hb : d111948 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83989, d111948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83989, d111948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83993 q = 1) (hb : d111952 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83993, d111952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20738 q ha hb
    | true =>
      simp only [d83993, d111952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro137 q hb ha
  have h6 (q : Pattern) (ha : d83994 q = 1) (hb : d111953 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83994, d111953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83994, d111953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83995 q = 1) (hb : d111954 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83995, d111954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83995, d111954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84004 q = 1) (hb : d111963 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84004, d111963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20740 q ha hb
    | true =>
      simp only [d84004, d111963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20733 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d83966 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d84005 q = 1) (hb : d111964 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84005, d111964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d84005, d111964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d84010 q = 1) (hb : d111969 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84010, d111969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20741 q ha hb
    | true =>
      simp only [d84010, d111969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d84011 q = 1) (hb : d111970 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84011, d111970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d84011, d111970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d84012 q = 1) (hb : d111971 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84012, d111971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84012, d111971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d84013 q = 1) (hb : d111972 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84013, d111972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84013, d111972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d84014 q = 1) (hb : d111973 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84014, d111973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84014, d111973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d84015 q = 1) (hb : d111974 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84015, d111974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84015, d111974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro20743 (p : Pattern) (ha : d84016 p = 1) (hb : d111975 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83960 q = 1) (hb : d98906 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83960, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14183 q ha hb
    | true =>
      simp only [d83960, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83961 q = 1) (hb : d98907 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83961, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83961, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d52451 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105 q ha hb
    | true =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83962 q = 1) (hb : d111921 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83962, d111921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83962, d111921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83963 q = 1) (hb : d111922 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83963, d111922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83963, d111922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d83984 q = 1) (hb : d111943 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83984, d111943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83984, d111943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84016 q = 1) (hb : d111975 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84016, d111975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84016, d111975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20744 (p : Pattern) (ha : d84021 p = 1) (hb : d111980 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83960 q = 1) (hb : d98906 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83960, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14183 q ha hb
    | true =>
      simp only [d83960, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83961 q = 1) (hb : d98907 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83961, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83961, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d52451 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105 q ha hb
    | true =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83962 q = 1) (hb : d111921 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83962, d111921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83962, d111921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83990 q = 1) (hb : d111949 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83990, d111949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83990, d111949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83991 q = 1) (hb : d111950 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83991, d111950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83991, d111950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84021 q = 1) (hb : d111980 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84021, d111980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84021, d111980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20745 (p : Pattern) (ha : d84025 p = 1) (hb : d111984 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83998 q = 1) (hb : d111957 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83998, d111957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20739 q ha hb
    | true =>
      simp only [d83998, d111957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83999 q = 1) (hb : d111958 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83999, d111958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83999, d111958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83960 q = 1) (hb : d98906 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83960, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14183 q ha hb
    | true =>
      simp only [d83960, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83961 q = 1) (hb : d98907 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83961, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83961, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84000 q = 1) (hb : d111959 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84000, d111959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84000, d111959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84001 q = 1) (hb : d111960 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84001, d111960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84001, d111960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84002 q = 1) (hb : d111961 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84002, d111961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84002, d111961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84025 q = 1) (hb : d111984 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84025, d111984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84025, d111984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20746 (p : Pattern) (ha : d84028 p = 1) (hb : d111987 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83960 q = 1) (hb : d98906 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83960, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14183 q ha hb
    | true =>
      simp only [d83960, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83961 q = 1) (hb : d98907 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83961, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83961, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84006 q = 1) (hb : d111965 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84006, d111965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84006, d111965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84007 q = 1) (hb : d111966 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84007, d111966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84007, d111966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84008 q = 1) (hb : d111967 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84008, d111967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84008, d111967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84028 q = 1) (hb : d111987 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84028, d111987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84028, d111987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20747 (p : Pattern) (ha : d84034 p = 1) (hb : d111993 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83986 q = 1) (hb : d111945 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83986, d111945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20737 q ha hb
    | true =>
      simp only [d83986, d111945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro135 q hb ha
  have h2 (q : Pattern) (ha : d83987 q = 1) (hb : d111946 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83987, d111946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83987, d111946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83988 q = 1) (hb : d111947 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83988, d111947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83988, d111947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83989 q = 1) (hb : d111948 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83989, d111948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83989, d111948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83993 q = 1) (hb : d111952 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83993, d111952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20738 q ha hb
    | true =>
      simp only [d83993, d111952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro137 q hb ha
  have h6 (q : Pattern) (ha : d83994 q = 1) (hb : d111953 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83994, d111953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83994, d111953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83995 q = 1) (hb : d111954 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83995, d111954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83995, d111954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84004 q = 1) (hb : d111963 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84004, d111963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20740 q ha hb
    | true =>
      simp only [d84004, d111963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20733 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d83966 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d84005 q = 1) (hb : d111964 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84005, d111964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d84005, d111964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d84010 q = 1) (hb : d111969 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84010, d111969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20741 q ha hb
    | true =>
      simp only [d84010, d111969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d84011 q = 1) (hb : d111970 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84011, d111970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d84011, d111970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d84012 q = 1) (hb : d111971 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84012, d111971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84012, d111971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d84013 q = 1) (hb : d111972 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84013, d111972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84013, d111972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d84014 q = 1) (hb : d111973 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84014, d111973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84014, d111973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d84017 q = 1) (hb : d111976 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84017, d111976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20743 q ha hb
    | true =>
      simp only [d84017, d111976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro141 q hb ha
  have h17 (q : Pattern) (ha : d84018 q = 1) (hb : d111977 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84018, d111977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84018, d111977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d84019 q = 1) (hb : d111978 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84019, d111978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d84019, d111978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d84020 q = 1) (hb : d111979 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84020, d111979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84020, d111979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d84022 q = 1) (hb : d111981 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84022, d111981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20744 q ha hb
    | true =>
      simp only [d84022, d111981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro143 q hb ha
  have h21 (q : Pattern) (ha : d84023 q = 1) (hb : d111982 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84023, d111982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84023, d111982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d84024 q = 1) (hb : d111983 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84024, d111983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d84024, d111983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d84026 q = 1) (hb : d111985 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84026, d111985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20745 q ha hb
    | true =>
      simp only [d84026, d111985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20735 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d83975 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d84027 q = 1) (hb : d111986 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84027, d111986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d84027, d111986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d84029 q = 1) (hb : d111988 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84029, d111988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20746 q ha hb
    | true =>
      simp only [d84029, d111988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d84030 q = 1) (hb : d111989 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84030, d111989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d84030, d111989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d84031 q = 1) (hb : d111990 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84031, d111990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d84031, d111990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d84032 q = 1) (hb : d111991 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84032, d111991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d84032, d111991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d84033 q = 1) (hb : d111992 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84033, d111992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d84033, d111992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d84034 q = 1) (hb : d111993 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84034, d111993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d84034, d111993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro20748 (p : Pattern) (ha : d84036 p = 1) (hb : d111995 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83966 q = 1) (hb : d111925 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83966, d111925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20733 q ha hb
    | true =>
      simp only [d83966, d111925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107 q hb ha
  have h2 (q : Pattern) (ha : d83967 q = 1) (hb : d111926 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83967, d111926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83967, d111926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83968 q = 1) (hb : d111927 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83968, d111927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83968, d111927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83969 q = 1) (hb : d111928 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83969, d111928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83969, d111928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83970 q = 1) (hb : d111929 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83970, d111929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83970, d111929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d939 q = 1) (hb : d52558 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d939, d52558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107 q ha hb
    | true =>
      simp only [d939, d52558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d940 q = 1) (hb : d52559 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d940, d52559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d940, d52559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d941 q = 1) (hb : d52560 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d941, d52560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d941, d52560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d942 q = 1) (hb : d52561 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d942, d52561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d942, d52561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d943 q = 1) (hb : d52562 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d943, d52562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d943, d52562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d84036 q = 1) (hb : d111995 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84036, d111995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84036, d111995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro20749 (p : Pattern) (ha : d84043 p = 1) (hb : d112002 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84026 q = 1) (hb : d111985 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84026, d111985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20745 q ha hb
    | true =>
      simp only [d84026, d111985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20735 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d83975 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d84027 q = 1) (hb : d111986 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84027, d111986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84027, d111986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d84029 q = 1) (hb : d111988 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84029, d111988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20746 q ha hb
    | true =>
      simp only [d84029, d111988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84030 q = 1) (hb : d111989 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84030, d111989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84030, d111989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84031 q = 1) (hb : d111990 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84031, d111990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84031, d111990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84041 q = 1) (hb : d112000 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84041, d112000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84041, d112000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84042 q = 1) (hb : d112001 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84042, d112001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84042, d112001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d84043 q = 1) (hb : d112002 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84043, d112002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84043, d112002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
end NetHack.Soko22Hazard87
