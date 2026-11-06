import NetHack.Soko22Hazard87.EqIntroBlocks0017
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem eqIntro4500 (p : Pattern) (selected : d6157 p = 2) : d6118 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d893 q = 2) : d770 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d893, d770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro804 q selected
    | true =>
      simp only [d893, d770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d894 q = 2) : d771 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d894, d771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d894, d771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d6154 q = 2) : d6115 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6154, d6115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d6154, d6115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d6155 q = 2) : d6116 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6155, d6116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d6155, d6116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d6156 q = 2) : d6117 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6156, d6117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d6156, d6117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d6157 q = 2) : d6118 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6157, d6118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6157, d6118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro4501 (p : Pattern) (selected : d6165 p = 2) : d6124 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d6139 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4497 q selected
    | true =>
      simp only [d6139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro788 q selected
  have h2 (q : Pattern) (selected : d6140 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d6141 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d6141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d6142 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d6146 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4498 q selected
    | true =>
      simp only [d6146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro790 q selected
  have h6 (q : Pattern) (selected : d6147 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d6148 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d6148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d6153 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4499 q selected
    | true =>
      simp only [d6153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3831 q selected
  have h9 (q : Pattern) (selected : d6158 q = 2) : d6119 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6158, d6119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4500 q selected
    | true =>
      simp only [d6158, d6119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro807 q selected
  have h10 (q : Pattern) (selected : d6159 q = 2) : d6120 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6159, d6120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d6159, d6120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d6160 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4493 q selected
    | true =>
      simp only [d6160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d6161 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d6161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d6162 q = 2) : d6121 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6162, d6121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d6162, d6121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d6163 q = 2) : d6122 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6163, d6122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d6163, d6122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d6164 q = 2) : d6123 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6164, d6123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d6164, d6123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d6165 q = 2) : d6124 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6165, d6124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6165, d6124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro4502 (p : Pattern) (selected : d6166 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d770 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro779 q selected
    | true =>
      simp only [d770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d771 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d6115 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d6115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d6116 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d6116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d6137 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d6166 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d6166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4503 (p : Pattern) (selected : d6171 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d770 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro779 q selected
    | true =>
      simp only [d770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d771 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d6115 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d6115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d6143 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d6144 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d6144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d6171 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d6171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4504 (p : Pattern) (selected : d6175 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d846 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro795 q selected
    | true =>
      simp only [d846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d847 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d6149 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d6149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d6150 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d6150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d6151 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d6151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d6175 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d6175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4505 (p : Pattern) (selected : d6176 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d4920 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d4920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3830 q selected
    | true =>
      simp only [d4920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d4921 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d4921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d4922 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d4922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d4922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d4923 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d4923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d4923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d4924 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d4924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d4924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d6176 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d6176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4506 (p : Pattern) (selected : d6178 p = 2) : d6127 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d893 q = 2) : d770 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d893, d770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro804 q selected
    | true =>
      simp only [d893, d770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d894 q = 2) : d771 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d894, d771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d894, d771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d6154 q = 2) : d6115 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6154, d6115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d6154, d6115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d6155 q = 2) : d6116 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6155, d6116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d6155, d6116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d6156 q = 2) : d6117 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6156, d6117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d6156, d6117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d6178 q = 2) : d6127 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6178, d6127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d6178, d6127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4507 (p : Pattern) (selected : d6186 p = 2) : d6133 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d6139 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4497 q selected
    | true =>
      simp only [d6139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro788 q selected
  have h2 (q : Pattern) (selected : d6140 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d6141 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d6141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d6142 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d6146 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4498 q selected
    | true =>
      simp only [d6146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro790 q selected
  have h6 (q : Pattern) (selected : d6147 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d6148 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d6148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d6153 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4499 q selected
    | true =>
      simp only [d6153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3831 q selected
  have h9 (q : Pattern) (selected : d6158 q = 2) : d6119 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6158, d6119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4500 q selected
    | true =>
      simp only [d6158, d6119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro807 q selected
  have h10 (q : Pattern) (selected : d6159 q = 2) : d6120 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6159, d6120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d6159, d6120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d6160 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4493 q selected
    | true =>
      simp only [d6160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d6161 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d6161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d6162 q = 2) : d6121 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6162, d6121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d6162, d6121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d6163 q = 2) : d6122 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6163, d6122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d6163, d6122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d6164 q = 2) : d6123 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6164, d6123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d6164, d6123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d6167 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4502 q selected
    | true =>
      simp only [d6167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro810 q selected
  have h17 (q : Pattern) (selected : d6168 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d6169 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d6169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d6170 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d6172 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4503 q selected
    | true =>
      simp only [d6172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro812 q selected
  have h21 (q : Pattern) (selected : d6173 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d6174 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d6174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d6177 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4504 q selected
    | true =>
      simp only [d6177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4505 q selected
  have h24 (q : Pattern) (selected : d6179 q = 2) : d6128 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6179, d6128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4506 q selected
    | true =>
      simp only [d6179, d6128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro815 q selected
  have h25 (q : Pattern) (selected : d6180 q = 2) : d6129 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6180, d6129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d6180, d6129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d6181 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4495 q selected
    | true =>
      simp only [d6181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d6182 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d6182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d6183 q = 2) : d6130 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6183, d6130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d6183, d6130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d6184 q = 2) : d6131 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6184, d6131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d6184, d6131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d6185 q = 2) : d6132 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6185, d6132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d6185, d6132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d6186 q = 2) : d6133 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6186, d6133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d6186, d6133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro4508 (p : Pattern) (selected : d6193 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d6188 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3831 q selected
    | true =>
      simp only [d6188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro782 q selected
  have h2 (q : Pattern) (selected : d6189 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d6190 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d6190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d6191 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d6192 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d939 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro782 q selected
    | true =>
      simp only [d939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d940 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d941 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d942 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d943 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d6193 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d6193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro4509 (p : Pattern) (selected : d6200 p = 2) : d82749 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d6177 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4504 q selected
    | true =>
      simp only [d6177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4505 q selected
  have h2 (q : Pattern) (selected : d6179 q = 2) : d6128 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6179, d6128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4506 q selected
    | true =>
      simp only [d6179, d6128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro815 q selected
  have h3 (q : Pattern) (selected : d6180 q = 2) : d6129 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6180, d6129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d6180, d6129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d6181 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4495 q selected
    | true =>
      simp only [d6181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d6182 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d6182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d6183 q = 2) : d6130 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6183, d6130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d6183, d6130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d6198 q = 2) : d6131 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6198, d6131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6198, d6131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d6199 q = 2) : d6132 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6199, d6132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6199, d6132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d6200 q = 2) : d82749 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6200, d82749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6200, d82749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro4510 (p : Pattern) (selected : d6209 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d993 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro825 q selected
    | true =>
      simp only [d993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d994 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d6206 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d6206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d6207 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d6207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d6208 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d6208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d6209 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d6209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4511 (p : Pattern) (selected : d6210 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d412 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro693 q selected
  have h2 (q : Pattern) (selected : d319 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro693 q selected
    | true =>
      simp only [d319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d413 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d320 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d414 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d415 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d971 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro775 q selected
  have h8 (q : Pattern) (selected : d751 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro775 q selected
    | true =>
      simp only [d751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d972 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d752 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d973 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d974 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d975 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d6210 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d6210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d6210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h14 p selected
theorem eqIntro4512 (p : Pattern) (selected : d6216 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d982 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro822 q selected
    | true =>
      simp only [d982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro823 q selected
  have h2 (q : Pattern) (selected : d983 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d984 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d987 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro823 q selected
    | true =>
      simp only [d987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro824 q selected
  have h5 (q : Pattern) (selected : d988 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d989 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d990 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d6211 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4511 q selected
    | true =>
      simp only [d6211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro824 q selected
  have h9 (q : Pattern) (selected : d6212 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d6213 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d6214 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d6214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d6215 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d6215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d6215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d6216 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d6216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d6216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro4513 (p : Pattern) (selected : d6222 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d6217 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4512 q selected
    | true =>
      simp only [d6217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d6218 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d6219 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d6219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d6220 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d6220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d6221 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d6221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d6222 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d6222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4514 (p : Pattern) (selected : d6227 p = 2) : d6233 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1037 q = 2) : d998 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1037, d998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro833 q selected
    | true =>
      simp only [d1037, d998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1038 q = 2) : d999 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1038, d999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1038, d999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d6224 q = 2) : d6230 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6224, d6230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d6224, d6230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d6225 q = 2) : d6231 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6225, d6231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d6225, d6231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d6226 q = 2) : d6232 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6226, d6232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d6226, d6232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d6227 q = 2) : d6233 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6227, d6233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d6227, d6233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4515 (p : Pattern) (selected : d6233 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d998 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro826 q selected
    | true =>
      simp only [d998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d999 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d6230 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d6230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d6231 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d6231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d6232 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d6232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d6233 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d6233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4516 (p : Pattern) (selected : d6239 p = 2) : d82760 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d6223 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4510 q selected
    | true =>
      simp only [d6223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4513 q selected
  have h2 (q : Pattern) (selected : d6228 q = 2) : d82755 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6228, d82755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4514 q selected
    | true =>
      simp only [d6228, d82755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro836 q selected
  have h3 (q : Pattern) (selected : d6229 q = 2) : d82756 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6229, d82756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d6229, d82756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d6234 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4515 q selected
    | true =>
      simp only [d6234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d6235 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d6235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d6236 q = 2) : d82757 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6236, d82757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d6236, d82757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d6237 q = 2) : d82758 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6237, d82758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6237, d82758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d6238 q = 2) : d82759 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6238, d82759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6238, d82759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d6239 q = 2) : d82760 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6239, d82760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6239, d82760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro4517 (p : Pattern) (selected : d6245 p = 2) : d82766 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d6125 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4494 q selected
  have h2 (q : Pattern) (selected : d6126 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d6126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d6134 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4494 q selected
    | true =>
      simp only [d6134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4496 q selected
  have h4 (q : Pattern) (selected : d6135 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d6135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d6136 q = 2) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d6136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d6136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d6187 q = 2) : d6134 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6187, d6134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4501 q selected
    | true =>
      simp only [d6187, d6134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4507 q selected
  have h7 (q : Pattern) (selected : d6194 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4508 q selected
    | true =>
      simp only [d6194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro818 q selected
  have h8 (q : Pattern) (selected : d6195 q = 2) : d6135 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6195, d6135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d6195, d6135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d6196 q = 2) : d82747 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d6196, d82747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d6196, d82747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d6197 q = 2) : d82748 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d6197, d82748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d6197, d82748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d6201 q = 2) : d82750 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6201, d82750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6201, d82750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4509 q selected
  have h12 (q : Pattern) (selected : d960 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro820 q selected
  have h13 (q : Pattern) (selected : d6202 q = 2) : d82751 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6202, d82751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d6202, d82751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d6203 q = 2) : d82752 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d6203, d82752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d6203, d82752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d6204 q = 2) : d82753 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d6204, d82753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d6204, d82753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d6205 q = 2) : d82754 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d6205, d82754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d6205, d82754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d6240 q = 2) : d82761 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6240, d82761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6240, d82761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4516 q selected
  have h18 (q : Pattern) (selected : d1070 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro839 q selected
  have h19 (q : Pattern) (selected : d6241 q = 2) : d82762 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6241, d82762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d6241, d82762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d6242 q = 2) : d82763 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d6242, d82763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d6242, d82763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d6243 q = 2) : d82764 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d6243, d82764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d6243, d82764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d6244 q = 2) : d82765 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d6244, d82765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d6244, d82765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d6245 q = 2) : d82766 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d6245, d82766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d6245, d82766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro4518 (p : Pattern) (selected : d6251 p = 2) : d82772 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d6246 q = 2) : d82767 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d6246, d82767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6246, d82767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4517 q selected
  have h2 (q : Pattern) (selected : d6247 q = 2) : d82768 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d6247, d82768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6247, d82768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d6248 q = 2) : d82769 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d6248, d82769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6248, d82769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d6249 q = 2) : d82770 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d6249, d82770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6249, d82770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d6250 q = 2) : d82771 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d6250, d82771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6250, d82771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d6251 q = 2) : d82772 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d6251, d82772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6251, d82772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro4519 (p : Pattern) (selected : d6257 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1149 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro851 q selected
    | true =>
      simp only [d1149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1150 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d6254 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d6254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d6255 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d6255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d6256 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d6256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d6257 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro4520 (p : Pattern) (selected : d6263 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d6258 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4519 q selected
    | true =>
      simp only [d6258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro854 q selected
  have h2 (q : Pattern) (selected : d6259 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d6260 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d6260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d6261 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d6262 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d6263 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro4521 (p : Pattern) (selected : d6266 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1149 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro851 q selected
    | true =>
      simp only [d1149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1150 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d6254 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d6254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d6255 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d6255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d6256 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d6256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d6266 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d6266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4522 (p : Pattern) (selected : d6272 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d6258 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4519 q selected
    | true =>
      simp only [d6258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro854 q selected
  have h2 (q : Pattern) (selected : d6259 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d6260 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d6260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d6261 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d6262 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d6267 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4521 q selected
    | true =>
      simp only [d6267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro857 q selected
  have h7 (q : Pattern) (selected : d6268 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d6269 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d6269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d6270 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d6271 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d6272 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d6272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro4523 (p : Pattern) (selected : d6277 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1149 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro851 q selected
    | true =>
      simp only [d1149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1150 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d6254 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d6254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d6255 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d6255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d6276 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d6277 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro4524 (p : Pattern) (selected : d6284 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1149 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro851 q selected
    | true =>
      simp only [d1149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1150 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d6254 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d6254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d6282 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d6283 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d6283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d6284 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro4525 (p : Pattern) (selected : d6291 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1222 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro867 q selected
    | true =>
      simp only [d1222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1223 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d6288 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d6288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d6289 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d6289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d6290 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d6290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d6291 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro4526 (p : Pattern) (selected : d6296 p = 2) : d6257 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1304 q = 2) : d1149 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1304, d1149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro880 q selected
    | true =>
      simp only [d1304, d1149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1305 q = 2) : d1150 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1305, d1150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1305, d1150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d6293 q = 2) : d6254 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6293, d6254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d6293, d6254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d6294 q = 2) : d6255 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6294, d6255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d6294, d6255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d6295 q = 2) : d6256 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6295, d6256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d6295, d6256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d6296 q = 2) : d6257 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6296, d6257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6296, d6257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro4527 (p : Pattern) (selected : d6304 p = 2) : d6263 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d6278 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4523 q selected
    | true =>
      simp only [d6278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro860 q selected
  have h2 (q : Pattern) (selected : d6279 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d6280 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d6280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d6281 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d6285 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4524 q selected
    | true =>
      simp only [d6285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro862 q selected
  have h6 (q : Pattern) (selected : d6286 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d6287 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d6287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d6292 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4525 q selected
    | true =>
      simp only [d6292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3846 q selected
  have h9 (q : Pattern) (selected : d6297 q = 2) : d6258 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6297, d6258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4526 q selected
    | true =>
      simp only [d6297, d6258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro883 q selected
  have h10 (q : Pattern) (selected : d6298 q = 2) : d6259 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6298, d6259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d6298, d6259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d6299 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4519 q selected
    | true =>
      simp only [d6299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d6300 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d6300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d6301 q = 2) : d6260 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6301, d6260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d6301, d6260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d6302 q = 2) : d6261 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6302, d6261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d6302, d6261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d6303 q = 2) : d6262 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6303, d6262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d6303, d6262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d6304 q = 2) : d6263 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6304, d6263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6304, d6263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro4528 (p : Pattern) (selected : d6305 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1149 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro851 q selected
    | true =>
      simp only [d1149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1150 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d6254 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d6254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d6255 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d6255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d6276 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d6305 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d6305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4529 (p : Pattern) (selected : d6310 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1149 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro851 q selected
    | true =>
      simp only [d1149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1150 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d6254 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d6254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d6282 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d6283 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d6283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d6310 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d6310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4530 (p : Pattern) (selected : d6314 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1222 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro867 q selected
    | true =>
      simp only [d1222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1223 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d6288 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d6288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d6289 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d6289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d6290 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d6290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d6314 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d6314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4531 (p : Pattern) (selected : d6315 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d5030 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d5030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3845 q selected
    | true =>
      simp only [d5030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d5031 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d5031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d5031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d5032 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d5032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d5033 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d5033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d5034 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d5034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d6315 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d6315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4532 (p : Pattern) (selected : d6317 p = 2) : d6266 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1304 q = 2) : d1149 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1304, d1149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro880 q selected
    | true =>
      simp only [d1304, d1149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1305 q = 2) : d1150 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1305, d1150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1305, d1150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d6293 q = 2) : d6254 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6293, d6254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d6293, d6254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d6294 q = 2) : d6255 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6294, d6255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d6294, d6255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d6295 q = 2) : d6256 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6295, d6256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d6295, d6256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d6317 q = 2) : d6266 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6317, d6266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d6317, d6266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4533 (p : Pattern) (selected : d6325 p = 2) : d6272 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d6278 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4523 q selected
    | true =>
      simp only [d6278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro860 q selected
  have h2 (q : Pattern) (selected : d6279 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d6280 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d6280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d6281 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d6285 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4524 q selected
    | true =>
      simp only [d6285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro862 q selected
  have h6 (q : Pattern) (selected : d6286 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d6287 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d6287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d6292 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4525 q selected
    | true =>
      simp only [d6292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3846 q selected
  have h9 (q : Pattern) (selected : d6297 q = 2) : d6258 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6297, d6258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4526 q selected
    | true =>
      simp only [d6297, d6258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro883 q selected
  have h10 (q : Pattern) (selected : d6298 q = 2) : d6259 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6298, d6259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d6298, d6259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d6299 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4519 q selected
    | true =>
      simp only [d6299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d6300 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d6300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d6301 q = 2) : d6260 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6301, d6260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d6301, d6260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d6302 q = 2) : d6261 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6302, d6261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d6302, d6261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d6303 q = 2) : d6262 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6303, d6262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d6303, d6262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d6306 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4528 q selected
    | true =>
      simp only [d6306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro886 q selected
  have h17 (q : Pattern) (selected : d6307 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d6308 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d6308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d6309 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d6311 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4529 q selected
    | true =>
      simp only [d6311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro888 q selected
  have h21 (q : Pattern) (selected : d6312 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d6313 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d6313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d6316 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4530 q selected
    | true =>
      simp only [d6316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4531 q selected
  have h24 (q : Pattern) (selected : d6318 q = 2) : d6267 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6318, d6267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4532 q selected
    | true =>
      simp only [d6318, d6267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro891 q selected
  have h25 (q : Pattern) (selected : d6319 q = 2) : d6268 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6319, d6268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d6319, d6268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d6320 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4521 q selected
    | true =>
      simp only [d6320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d6321 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d6321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d6322 q = 2) : d6269 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6322, d6269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d6322, d6269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d6323 q = 2) : d6270 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6323, d6270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d6323, d6270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d6324 q = 2) : d6271 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6324, d6271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d6324, d6271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d6325 q = 2) : d6272 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6325, d6272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d6325, d6272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro4534 (p : Pattern) (selected : d6332 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d6327 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3846 q selected
    | true =>
      simp only [d6327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro854 q selected
  have h2 (q : Pattern) (selected : d6328 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d6329 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d6329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d6330 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d6331 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1350 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro854 q selected
    | true =>
      simp only [d1350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d1351 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d1352 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d1352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d1353 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d1354 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d6332 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d6332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro4535 (p : Pattern) (selected : d6339 p = 2) : d82777 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d6316 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4530 q selected
    | true =>
      simp only [d6316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4531 q selected
  have h2 (q : Pattern) (selected : d6318 q = 2) : d6267 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6318, d6267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4532 q selected
    | true =>
      simp only [d6318, d6267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro891 q selected
  have h3 (q : Pattern) (selected : d6319 q = 2) : d6268 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6319, d6268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d6319, d6268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d6320 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4521 q selected
    | true =>
      simp only [d6320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d6321 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d6321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d6322 q = 2) : d6269 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6322, d6269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d6322, d6269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d6337 q = 2) : d6270 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6337, d6270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6337, d6270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d6338 q = 2) : d6271 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6338, d6271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6338, d6271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d6339 q = 2) : d82777 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6339, d82777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6339, d82777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro4536 (p : Pattern) (selected : d6348 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1418 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro901 q selected
    | true =>
      simp only [d1418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1419 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d6345 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d6345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d6346 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d6346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d6347 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d6347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d6348 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d6348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4537 (p : Pattern) (selected : d6349 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1385 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro845 q selected
  have h2 (q : Pattern) (selected : d1110 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro845 q selected
    | true =>
      simp only [d1110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1386 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1111 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1387 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1388 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d1391 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro846 q selected
  have h8 (q : Pattern) (selected : d1121 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro846 q selected
    | true =>
      simp only [d1121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d1392 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d1392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d1122 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d1122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d1393 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d1393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d1394 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d1394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d1395 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d1395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d6349 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d6349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d6349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h14 p selected
theorem eqIntro4538 (p : Pattern) (selected : d6355 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d6350 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d6350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3843 q selected
  have h2 (q : Pattern) (selected : d5018 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3843 q selected
    | true =>
      simp only [d5018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d6351 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d6351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d6351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d5019 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d5019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d6352 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d6352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d6352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d6353 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d6353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d6353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d6354 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d6354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d6354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d6355 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d6355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d6355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro4539 (p : Pattern) (selected : d6361 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1402 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro898 q selected
    | true =>
      simp only [d1402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro899 q selected
  have h2 (q : Pattern) (selected : d1403 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1404 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1412 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro899 q selected
    | true =>
      simp only [d1412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro900 q selected
  have h5 (q : Pattern) (selected : d1413 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1414 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d1415 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d6356 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4537 q selected
    | true =>
      simp only [d6356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4538 q selected
  have h9 (q : Pattern) (selected : d6357 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d6358 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d6359 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d6359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d6360 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d6360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d6360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d6361 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d6361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d6361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro4540 (p : Pattern) (selected : d6367 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d6362 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4539 q selected
    | true =>
      simp only [d6362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d6363 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d6364 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d6364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d6365 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d6365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d6366 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d6366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d6367 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d6367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4541 (p : Pattern) (selected : d6372 p = 2) : d6378 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1471 q = 2) : d1423 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1471, d1423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro909 q selected
    | true =>
      simp only [d1471, d1423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1472 q = 2) : d1424 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1472, d1424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1472, d1424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d6369 q = 2) : d6375 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6369, d6375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d6369, d6375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d6370 q = 2) : d6376 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6370, d6376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d6370, d6376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d6371 q = 2) : d6377 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6371, d6377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d6371, d6377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d6372 q = 2) : d6378 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6372, d6378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d6372, d6378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4542 (p : Pattern) (selected : d6378 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1423 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro902 q selected
    | true =>
      simp only [d1423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1424 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d6375 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d6375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d6376 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d6376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d6377 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d6377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d6378 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d6378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4543 (p : Pattern) (selected : d6384 p = 2) : d82788 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d6368 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4536 q selected
    | true =>
      simp only [d6368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4540 q selected
  have h2 (q : Pattern) (selected : d6373 q = 2) : d82783 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6373, d82783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4541 q selected
    | true =>
      simp only [d6373, d82783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro912 q selected
  have h3 (q : Pattern) (selected : d6374 q = 2) : d82784 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6374, d82784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d6374, d82784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d6379 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4542 q selected
    | true =>
      simp only [d6379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d6380 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d6380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d6381 q = 2) : d82785 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6381, d82785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d6381, d82785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d6382 q = 2) : d82786 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6382, d82786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6382, d82786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d6383 q = 2) : d82787 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6383, d82787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6383, d82787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d6384 q = 2) : d82788 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6384, d82788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6384, d82788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro4544 (p : Pattern) (selected : d6390 p = 2) : d82794 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d6264 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4520 q selected
  have h2 (q : Pattern) (selected : d6265 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d6265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d6273 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4520 q selected
    | true =>
      simp only [d6273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4522 q selected
  have h4 (q : Pattern) (selected : d6274 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d6274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d6275 q = 2) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d6275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d6275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d6326 q = 2) : d6273 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6326, d6273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4527 q selected
    | true =>
      simp only [d6326, d6273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4533 q selected
  have h7 (q : Pattern) (selected : d6333 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4534 q selected
    | true =>
      simp only [d6333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro894 q selected
  have h8 (q : Pattern) (selected : d6334 q = 2) : d6274 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6334, d6274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d6334, d6274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d6335 q = 2) : d82775 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d6335, d82775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d6335, d82775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d6336 q = 2) : d82776 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d6336, d82776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d6336, d82776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d6340 q = 2) : d82778 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6340, d82778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6340, d82778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4535 q selected
  have h12 (q : Pattern) (selected : d1371 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro896 q selected
  have h13 (q : Pattern) (selected : d6341 q = 2) : d82779 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6341, d82779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d6341, d82779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d6342 q = 2) : d82780 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d6342, d82780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d6342, d82780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d6343 q = 2) : d82781 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d6343, d82781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d6343, d82781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d6344 q = 2) : d82782 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d6344, d82782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d6344, d82782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d6385 q = 2) : d82789 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6385, d82789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6385, d82789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4543 q selected
  have h18 (q : Pattern) (selected : d1504 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro915 q selected
  have h19 (q : Pattern) (selected : d6386 q = 2) : d82790 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6386, d82790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d6386, d82790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d6387 q = 2) : d82791 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d6387, d82791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d6387, d82791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d6388 q = 2) : d82792 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d6388, d82792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d6388, d82792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d6389 q = 2) : d82793 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d6389, d82793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d6389, d82793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d6390 q = 2) : d82794 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d6390, d82794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d6390, d82794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro4545 (p : Pattern) (selected : d6396 p = 2) : d82800 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d6391 q = 2) : d82795 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d6391, d82795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6391, d82795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4544 q selected
  have h2 (q : Pattern) (selected : d6392 q = 2) : d82796 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d6392, d82796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6392, d82796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d6393 q = 2) : d82797 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d6393, d82797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6393, d82797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d6394 q = 2) : d82798 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d6394, d82798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6394, d82798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d6395 q = 2) : d82799 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d6395, d82799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6395, d82799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d6396 q = 2) : d82800 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d6396, d82800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6396, d82800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro4546 (p : Pattern) (selected : d6403 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1610 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro933 q selected
    | true =>
      simp only [d1610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1611 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d6400 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d6400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d6401 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d6401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d6402 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d6402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d6403 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro4547 (p : Pattern) (selected : d6409 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d6404 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4546 q selected
    | true =>
      simp only [d6404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro936 q selected
  have h2 (q : Pattern) (selected : d6405 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d6406 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d6406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d6407 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d6408 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d6409 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro4548 (p : Pattern) (selected : d6412 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1610 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro933 q selected
    | true =>
      simp only [d1610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1611 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d6400 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d6400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d6401 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d6401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d6402 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d6402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d6412 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d6412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4549 (p : Pattern) (selected : d6418 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d6404 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4546 q selected
    | true =>
      simp only [d6404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro936 q selected
  have h2 (q : Pattern) (selected : d6405 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d6406 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d6406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d6407 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d6408 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d6413 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4548 q selected
    | true =>
      simp only [d6413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro939 q selected
  have h7 (q : Pattern) (selected : d6414 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d6415 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d6415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d6416 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d6417 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d6418 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d6418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro4550 (p : Pattern) (selected : d6423 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1610 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro933 q selected
    | true =>
      simp only [d1610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1611 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d6400 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d6400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d6401 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d6401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d6422 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d6423 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro4551 (p : Pattern) (selected : d6430 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1610 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro933 q selected
    | true =>
      simp only [d1610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1611 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d6400 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d6400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d6428 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d6429 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d6429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d6430 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro4552 (p : Pattern) (selected : d6437 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1677 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro947 q selected
    | true =>
      simp only [d1677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1678 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d6434 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d6434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d6435 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d6435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d6436 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d6436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d6437 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro4553 (p : Pattern) (selected : d6442 p = 2) : d6403 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1781 q = 2) : d1610 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1781, d1610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro966 q selected
    | true =>
      simp only [d1781, d1610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1782 q = 2) : d1611 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1782, d1611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1782, d1611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d6439 q = 2) : d6400 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6439, d6400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d6439, d6400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d6440 q = 2) : d6401 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6440, d6401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d6440, d6401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d6441 q = 2) : d6402 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6441, d6402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d6441, d6402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d6442 q = 2) : d6403 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6442, d6403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6442, d6403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro4554 (p : Pattern) (selected : d6450 p = 2) : d6409 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d6424 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4550 q selected
    | true =>
      simp only [d6424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro942 q selected
  have h2 (q : Pattern) (selected : d6425 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d6426 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d6426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d6427 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d6431 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4551 q selected
    | true =>
      simp only [d6431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro944 q selected
  have h6 (q : Pattern) (selected : d6432 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d6433 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d6433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d6438 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4552 q selected
    | true =>
      simp only [d6438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3861 q selected
  have h9 (q : Pattern) (selected : d6443 q = 2) : d6404 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6443, d6404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4553 q selected
    | true =>
      simp only [d6443, d6404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro969 q selected
  have h10 (q : Pattern) (selected : d6444 q = 2) : d6405 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6444, d6405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d6444, d6405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d6445 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4546 q selected
    | true =>
      simp only [d6445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d6446 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d6446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d6447 q = 2) : d6406 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6447, d6406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d6447, d6406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d6448 q = 2) : d6407 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6448, d6407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d6448, d6407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d6449 q = 2) : d6408 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6449, d6408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d6449, d6408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d6450 q = 2) : d6409 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6450, d6409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6450, d6409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro4555 (p : Pattern) (selected : d6451 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1610 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro933 q selected
    | true =>
      simp only [d1610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1611 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d6400 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d6400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d6401 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d6401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d6422 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d6451 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d6451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4556 (p : Pattern) (selected : d6456 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1610 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro933 q selected
    | true =>
      simp only [d1610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1611 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d6400 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d6400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d6428 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d6429 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d6429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d6456 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d6456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4557 (p : Pattern) (selected : d6460 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1677 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro947 q selected
    | true =>
      simp only [d1677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1678 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d6434 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d6434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d6435 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d6435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d6436 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d6436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d6460 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d6460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4558 (p : Pattern) (selected : d6461 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d5146 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d5146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3860 q selected
    | true =>
      simp only [d5146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d5147 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d5147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d5147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d5148 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d5148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d5149 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d5149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d5150 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d5150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d6461 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d6461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4559 (p : Pattern) (selected : d6463 p = 2) : d6412 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1781 q = 2) : d1610 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1781, d1610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro966 q selected
    | true =>
      simp only [d1781, d1610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1782 q = 2) : d1611 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1782, d1611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1782, d1611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d6439 q = 2) : d6400 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6439, d6400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d6439, d6400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d6440 q = 2) : d6401 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6440, d6401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d6440, d6401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d6441 q = 2) : d6402 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6441, d6402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d6441, d6402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d6463 q = 2) : d6412 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6463, d6412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d6463, d6412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4560 (p : Pattern) (selected : d6471 p = 2) : d6418 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d6424 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4550 q selected
    | true =>
      simp only [d6424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro942 q selected
  have h2 (q : Pattern) (selected : d6425 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d6426 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d6426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d6427 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d6431 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4551 q selected
    | true =>
      simp only [d6431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro944 q selected
  have h6 (q : Pattern) (selected : d6432 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d6433 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d6433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d6438 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4552 q selected
    | true =>
      simp only [d6438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3861 q selected
  have h9 (q : Pattern) (selected : d6443 q = 2) : d6404 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6443, d6404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4553 q selected
    | true =>
      simp only [d6443, d6404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro969 q selected
  have h10 (q : Pattern) (selected : d6444 q = 2) : d6405 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6444, d6405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d6444, d6405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d6445 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4546 q selected
    | true =>
      simp only [d6445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d6446 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d6446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d6447 q = 2) : d6406 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6447, d6406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d6447, d6406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d6448 q = 2) : d6407 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6448, d6407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d6448, d6407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d6449 q = 2) : d6408 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6449, d6408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d6449, d6408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d6452 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4555 q selected
    | true =>
      simp only [d6452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro972 q selected
  have h17 (q : Pattern) (selected : d6453 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d6454 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d6454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d6455 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d6457 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4556 q selected
    | true =>
      simp only [d6457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro974 q selected
  have h21 (q : Pattern) (selected : d6458 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d6459 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d6459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d6462 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4557 q selected
    | true =>
      simp only [d6462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4558 q selected
  have h24 (q : Pattern) (selected : d6464 q = 2) : d6413 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6464, d6413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4559 q selected
    | true =>
      simp only [d6464, d6413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro977 q selected
  have h25 (q : Pattern) (selected : d6465 q = 2) : d6414 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6465, d6414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d6465, d6414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d6466 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4548 q selected
    | true =>
      simp only [d6466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d6467 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d6467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d6468 q = 2) : d6415 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6468, d6415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d6468, d6415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d6469 q = 2) : d6416 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6469, d6416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d6469, d6416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d6470 q = 2) : d6417 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6470, d6417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d6470, d6417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d6471 q = 2) : d6418 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6471, d6418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d6471, d6418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro4561 (p : Pattern) (selected : d6478 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d6473 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3861 q selected
    | true =>
      simp only [d6473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro936 q selected
  have h2 (q : Pattern) (selected : d6474 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d6475 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d6475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d6476 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d6477 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1827 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro936 q selected
    | true =>
      simp only [d1827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d1828 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d1829 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d1829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d1830 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d1831 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d6478 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d6478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro4562 (p : Pattern) (selected : d6485 p = 2) : d82806 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d6462 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4557 q selected
    | true =>
      simp only [d6462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4558 q selected
  have h2 (q : Pattern) (selected : d6464 q = 2) : d6413 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6464, d6413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4559 q selected
    | true =>
      simp only [d6464, d6413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro977 q selected
  have h3 (q : Pattern) (selected : d6465 q = 2) : d6414 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6465, d6414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d6465, d6414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d6466 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4548 q selected
    | true =>
      simp only [d6466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d6467 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d6467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d6468 q = 2) : d6415 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6468, d6415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d6468, d6415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d6483 q = 2) : d6416 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6483, d6416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6483, d6416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d6484 q = 2) : d6417 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6484, d6417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6484, d6417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d6485 q = 2) : d82806 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6485, d82806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6485, d82806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro4563 (p : Pattern) (selected : d6494 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1895 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro987 q selected
    | true =>
      simp only [d1895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1896 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d6491 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d6491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d6492 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d6492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d6493 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d6493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d6494 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d6494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4564 (p : Pattern) (selected : d6495 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1862 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro927 q selected
  have h2 (q : Pattern) (selected : d1570 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro927 q selected
    | true =>
      simp only [d1570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1863 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1571 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1864 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1865 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d1868 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro928 q selected
  have h8 (q : Pattern) (selected : d1582 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro928 q selected
    | true =>
      simp only [d1582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d1869 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d1869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d1583 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d1583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d1870 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d1870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d1871 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d1871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d1872 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d1872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d6495 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d6495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d6495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h14 p selected
theorem eqIntro4565 (p : Pattern) (selected : d6501 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d6496 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d6496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3858 q selected
  have h2 (q : Pattern) (selected : d5134 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3858 q selected
    | true =>
      simp only [d5134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d6497 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d6497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d6497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d5135 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d5135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d6498 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d6498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d6498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d6499 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d6499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d6499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d6500 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d6500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d6500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d6501 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d6501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d6501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro4566 (p : Pattern) (selected : d6507 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1879 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro984 q selected
    | true =>
      simp only [d1879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro985 q selected
  have h2 (q : Pattern) (selected : d1880 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1881 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1889 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro985 q selected
    | true =>
      simp only [d1889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro986 q selected
  have h5 (q : Pattern) (selected : d1890 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1891 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d1892 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d6502 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4564 q selected
    | true =>
      simp only [d6502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4565 q selected
  have h9 (q : Pattern) (selected : d6503 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d6504 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d6505 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d6505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d6506 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d6506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d6506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d6507 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d6507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d6507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro4567 (p : Pattern) (selected : d6513 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d6508 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4566 q selected
    | true =>
      simp only [d6508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d6509 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d6510 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d6510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d6511 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d6511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d6512 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d6512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d6513 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d6513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4568 (p : Pattern) (selected : d6518 p = 2) : d6524 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1948 q = 2) : d1900 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1948, d1900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro995 q selected
    | true =>
      simp only [d1948, d1900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1949 q = 2) : d1901 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1949, d1901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1949, d1901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d6515 q = 2) : d6521 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6515, d6521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d6515, d6521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d6516 q = 2) : d6522 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6516, d6522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d6516, d6522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d6517 q = 2) : d6523 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6517, d6523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d6517, d6523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d6518 q = 2) : d6524 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6518, d6524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d6518, d6524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4569 (p : Pattern) (selected : d6524 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1900 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro988 q selected
    | true =>
      simp only [d1900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1901 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d6521 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d6521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d6522 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d6522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d6523 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d6523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d6524 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d6524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4570 (p : Pattern) (selected : d6530 p = 2) : d82817 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d6514 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4563 q selected
    | true =>
      simp only [d6514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4567 q selected
  have h2 (q : Pattern) (selected : d6519 q = 2) : d82812 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6519, d82812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4568 q selected
    | true =>
      simp only [d6519, d82812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro998 q selected
  have h3 (q : Pattern) (selected : d6520 q = 2) : d82813 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6520, d82813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d6520, d82813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d6525 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4569 q selected
    | true =>
      simp only [d6525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d6526 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d6526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d6527 q = 2) : d82814 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6527, d82814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d6527, d82814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d6528 q = 2) : d82815 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6528, d82815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6528, d82815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d6529 q = 2) : d82816 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6529, d82816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6529, d82816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d6530 q = 2) : d82817 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6530, d82817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6530, d82817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro4571 (p : Pattern) (selected : d6536 p = 2) : d82823 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d6410 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4547 q selected
  have h2 (q : Pattern) (selected : d6411 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d6411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d6419 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4547 q selected
    | true =>
      simp only [d6419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4549 q selected
  have h4 (q : Pattern) (selected : d6420 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d6420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d6421 q = 2) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d6421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d6421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d6472 q = 2) : d6419 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6472, d6419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4554 q selected
    | true =>
      simp only [d6472, d6419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4560 q selected
  have h7 (q : Pattern) (selected : d6479 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4561 q selected
    | true =>
      simp only [d6479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro980 q selected
  have h8 (q : Pattern) (selected : d6480 q = 2) : d6420 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6480, d6420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d6480, d6420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d6481 q = 2) : d82804 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d6481, d82804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d6481, d82804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d6482 q = 2) : d82805 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d6482, d82805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d6482, d82805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d6486 q = 2) : d82807 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6486, d82807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6486, d82807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4562 q selected
  have h12 (q : Pattern) (selected : d1848 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro982 q selected
  have h13 (q : Pattern) (selected : d6487 q = 2) : d82808 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6487, d82808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d6487, d82808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d6488 q = 2) : d82809 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d6488, d82809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d6488, d82809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d6489 q = 2) : d82810 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d6489, d82810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d6489, d82810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d6490 q = 2) : d82811 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d6490, d82811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d6490, d82811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d6531 q = 2) : d82818 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6531, d82818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6531, d82818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4570 q selected
  have h18 (q : Pattern) (selected : d1981 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1001 q selected
  have h19 (q : Pattern) (selected : d6532 q = 2) : d82819 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6532, d82819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d6532, d82819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d6533 q = 2) : d82820 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d6533, d82820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d6533, d82820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d6534 q = 2) : d82821 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d6534, d82821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d6534, d82821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d6535 q = 2) : d82822 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d6535, d82822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d6535, d82822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d6536 q = 2) : d82823 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d6536, d82823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d6536, d82823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro4572 (p : Pattern) (selected : d6542 p = 2) : d82829 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d6537 q = 2) : d82824 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d6537, d82824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6537, d82824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4571 q selected
  have h2 (q : Pattern) (selected : d6538 q = 2) : d82825 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d6538, d82825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6538, d82825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d6539 q = 2) : d82826 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d6539, d82826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6539, d82826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d6540 q = 2) : d82827 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d6540, d82827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6540, d82827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d6541 q = 2) : d82828 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d6541, d82828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6541, d82828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d6542 q = 2) : d82829 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d6542, d82829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6542, d82829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro4573 (p : Pattern) (selected : d6550 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2093 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1022 q selected
    | true =>
      simp only [d2093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2094 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d6547 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d6547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d6548 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d6548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d6549 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d6549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d6550 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro4574 (p : Pattern) (selected : d6556 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d6551 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4573 q selected
    | true =>
      simp only [d6551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1025 q selected
  have h2 (q : Pattern) (selected : d6552 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d6553 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d6553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d6554 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d6555 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d6556 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro4575 (p : Pattern) (selected : d6559 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2093 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1022 q selected
    | true =>
      simp only [d2093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2094 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d6547 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d6547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d6548 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d6548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d6549 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d6549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d6559 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d6559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4576 (p : Pattern) (selected : d6565 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d6551 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4573 q selected
    | true =>
      simp only [d6551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1025 q selected
  have h2 (q : Pattern) (selected : d6552 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d6553 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d6553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d6554 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d6555 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d6560 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4575 q selected
    | true =>
      simp only [d6560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1028 q selected
  have h7 (q : Pattern) (selected : d6561 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d6562 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d6562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d6563 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d6564 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d6565 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d6565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro4577 (p : Pattern) (selected : d6570 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2093 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1022 q selected
    | true =>
      simp only [d2093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2094 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d6547 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d6547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d6548 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d6548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d6569 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d6570 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro4578 (p : Pattern) (selected : d6577 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2093 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1022 q selected
    | true =>
      simp only [d2093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2094 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d6547 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d6547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d6575 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d6576 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d6576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d6577 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro4579 (p : Pattern) (selected : d6584 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2156 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1036 q selected
    | true =>
      simp only [d2156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2157 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d6581 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d6581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d6582 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d6582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d6583 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d6583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d6584 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro4580 (p : Pattern) (selected : d6589 p = 2) : d6550 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2259 q = 2) : d2093 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2259, d2093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1056 q selected
    | true =>
      simp only [d2259, d2093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2260 q = 2) : d2094 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2260, d2094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2260, d2094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d6586 q = 2) : d6547 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6586, d6547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d6586, d6547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d6587 q = 2) : d6548 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6587, d6548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d6587, d6548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d6588 q = 2) : d6549 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6588, d6549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d6588, d6549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d6589 q = 2) : d6550 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6589, d6550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6589, d6550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro4581 (p : Pattern) (selected : d6597 p = 2) : d6556 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d6571 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4577 q selected
    | true =>
      simp only [d6571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1031 q selected
  have h2 (q : Pattern) (selected : d6572 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d6573 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d6573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d6574 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d6578 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4578 q selected
    | true =>
      simp only [d6578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1033 q selected
  have h6 (q : Pattern) (selected : d6579 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d6580 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d6580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d6585 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4579 q selected
    | true =>
      simp only [d6585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3875 q selected
  have h9 (q : Pattern) (selected : d6590 q = 2) : d6551 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6590, d6551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4580 q selected
    | true =>
      simp only [d6590, d6551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1059 q selected
  have h10 (q : Pattern) (selected : d6591 q = 2) : d6552 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6591, d6552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d6591, d6552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d6592 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4573 q selected
    | true =>
      simp only [d6592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d6593 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d6593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d6594 q = 2) : d6553 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6594, d6553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d6594, d6553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d6595 q = 2) : d6554 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6595, d6554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d6595, d6554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d6596 q = 2) : d6555 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6596, d6555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d6596, d6555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d6597 q = 2) : d6556 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6597, d6556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6597, d6556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro4582 (p : Pattern) (selected : d6598 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2093 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1022 q selected
    | true =>
      simp only [d2093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2094 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d6547 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d6547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d6548 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d6548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d6569 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d6598 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d6598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4583 (p : Pattern) (selected : d6603 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2093 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1022 q selected
    | true =>
      simp only [d2093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2094 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d6547 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d6547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d6575 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d6576 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d6576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d6603 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d6603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4584 (p : Pattern) (selected : d6607 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2156 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1036 q selected
    | true =>
      simp only [d2156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2157 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d6581 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d6581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d6582 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d6582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d6583 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d6583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d6607 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d6607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4585 (p : Pattern) (selected : d6608 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d5259 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d5259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3874 q selected
    | true =>
      simp only [d5259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d5260 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d5260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d5260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d5261 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d5261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d5262 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d5262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d5263 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d5263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d6608 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d6608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4586 (p : Pattern) (selected : d6610 p = 2) : d6559 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2259 q = 2) : d2093 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2259, d2093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1056 q selected
    | true =>
      simp only [d2259, d2093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2260 q = 2) : d2094 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2260, d2094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2260, d2094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d6586 q = 2) : d6547 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6586, d6547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d6586, d6547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d6587 q = 2) : d6548 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6587, d6548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d6587, d6548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d6588 q = 2) : d6549 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6588, d6549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d6588, d6549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d6610 q = 2) : d6559 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6610, d6559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d6610, d6559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4587 (p : Pattern) (selected : d6618 p = 2) : d6565 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d6571 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4577 q selected
    | true =>
      simp only [d6571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1031 q selected
  have h2 (q : Pattern) (selected : d6572 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d6573 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d6573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d6574 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d6578 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4578 q selected
    | true =>
      simp only [d6578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1033 q selected
  have h6 (q : Pattern) (selected : d6579 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d6580 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d6580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d6585 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4579 q selected
    | true =>
      simp only [d6585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3875 q selected
  have h9 (q : Pattern) (selected : d6590 q = 2) : d6551 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6590, d6551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4580 q selected
    | true =>
      simp only [d6590, d6551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1059 q selected
  have h10 (q : Pattern) (selected : d6591 q = 2) : d6552 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6591, d6552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d6591, d6552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d6592 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4573 q selected
    | true =>
      simp only [d6592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d6593 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d6593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d6594 q = 2) : d6553 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6594, d6553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d6594, d6553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d6595 q = 2) : d6554 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6595, d6554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d6595, d6554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d6596 q = 2) : d6555 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6596, d6555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d6596, d6555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d6599 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4582 q selected
    | true =>
      simp only [d6599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1062 q selected
  have h17 (q : Pattern) (selected : d6600 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d6601 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d6601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d6602 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d6604 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4583 q selected
    | true =>
      simp only [d6604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1064 q selected
  have h21 (q : Pattern) (selected : d6605 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d6606 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d6606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d6609 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4584 q selected
    | true =>
      simp only [d6609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4585 q selected
  have h24 (q : Pattern) (selected : d6611 q = 2) : d6560 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6611, d6560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4586 q selected
    | true =>
      simp only [d6611, d6560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1067 q selected
  have h25 (q : Pattern) (selected : d6612 q = 2) : d6561 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6612, d6561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d6612, d6561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d6613 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4575 q selected
    | true =>
      simp only [d6613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d6614 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d6614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d6615 q = 2) : d6562 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6615, d6562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d6615, d6562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d6616 q = 2) : d6563 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6616, d6563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d6616, d6563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d6617 q = 2) : d6564 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6617, d6564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d6617, d6564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d6618 q = 2) : d6565 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6618, d6565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d6618, d6565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro4588 (p : Pattern) (selected : d6625 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d6620 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3875 q selected
    | true =>
      simp only [d6620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1025 q selected
  have h2 (q : Pattern) (selected : d6621 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d6622 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d6622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d6623 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d6624 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d2305 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1025 q selected
    | true =>
      simp only [d2305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d2306 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d2307 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d2307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d2308 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d2309 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d6625 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d6625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro4589 (p : Pattern) (selected : d6632 p = 2) : d82836 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d6609 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4584 q selected
    | true =>
      simp only [d6609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4585 q selected
  have h2 (q : Pattern) (selected : d6611 q = 2) : d6560 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6611, d6560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4586 q selected
    | true =>
      simp only [d6611, d6560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1067 q selected
  have h3 (q : Pattern) (selected : d6612 q = 2) : d6561 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6612, d6561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d6612, d6561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d6613 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4575 q selected
    | true =>
      simp only [d6613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d6614 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d6614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d6615 q = 2) : d6562 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6615, d6562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d6615, d6562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d6630 q = 2) : d6563 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6630, d6563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6630, d6563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d6631 q = 2) : d6564 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6631, d6564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6631, d6564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d6632 q = 2) : d82836 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6632, d82836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6632, d82836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro4590 (p : Pattern) (selected : d6641 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2373 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1077 q selected
    | true =>
      simp only [d2373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2374 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d6638 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d6638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d6639 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d6639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d6640 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d6640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d6641 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d6641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4591 (p : Pattern) (selected : d6642 p = 2) : d0 p = 1 := by
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
  have h4 (q : Pattern) (selected : d2054 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2342 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d2343 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d2346 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1017 q selected
  have h8 (q : Pattern) (selected : d2065 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1017 q selected
    | true =>
      simp only [d2065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d2347 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d2347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d2066 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d2066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d2348 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d2348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d2349 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d2349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d2350 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d2350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d6642 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d6642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d6642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h14 p selected
theorem eqIntro4592 (p : Pattern) (selected : d6648 p = 2) : d0 p = 1 := by
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
  have h4 (q : Pattern) (selected : d5248 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d5248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d6645 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d6645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d6645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d6646 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d6646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d6646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d6647 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d6647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d6647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d6648 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d6648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d6648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro4593 (p : Pattern) (selected : d6654 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2357 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1074 q selected
    | true =>
      simp only [d2357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1075 q selected
  have h2 (q : Pattern) (selected : d2358 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2359 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2367 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1075 q selected
    | true =>
      simp only [d2367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1076 q selected
  have h5 (q : Pattern) (selected : d2368 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d2369 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d2370 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d6649 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4591 q selected
    | true =>
      simp only [d6649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4592 q selected
  have h9 (q : Pattern) (selected : d6650 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d6651 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d6652 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d6652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d6653 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d6653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d6653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d6654 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d6654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d6654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro4594 (p : Pattern) (selected : d6660 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d6655 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4593 q selected
    | true =>
      simp only [d6655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d6656 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d6657 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d6657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d6658 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d6658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d6659 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d6659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d6660 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d6660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4595 (p : Pattern) (selected : d6665 p = 2) : d6671 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2426 q = 2) : d2378 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2426, d2378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1085 q selected
    | true =>
      simp only [d2426, d2378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2427 q = 2) : d2379 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2427, d2379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2427, d2379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d6662 q = 2) : d6668 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6662, d6668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d6662, d6668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d6663 q = 2) : d6669 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6663, d6669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d6663, d6669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d6664 q = 2) : d6670 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6664, d6670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d6664, d6670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d6665 q = 2) : d6671 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6665, d6671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d6665, d6671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4596 (p : Pattern) (selected : d6671 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2378 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1078 q selected
    | true =>
      simp only [d2378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2379 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d6668 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d6668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d6669 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d6669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d6670 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d6670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d6671 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d6671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4597 (p : Pattern) (selected : d6677 p = 2) : d82847 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d6661 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4590 q selected
    | true =>
      simp only [d6661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4594 q selected
  have h2 (q : Pattern) (selected : d6666 q = 2) : d82842 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6666, d82842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4595 q selected
    | true =>
      simp only [d6666, d82842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1088 q selected
  have h3 (q : Pattern) (selected : d6667 q = 2) : d82843 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6667, d82843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d6667, d82843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d6672 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4596 q selected
    | true =>
      simp only [d6672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d6673 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d6673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d6674 q = 2) : d82844 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6674, d82844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d6674, d82844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d6675 q = 2) : d82845 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6675, d82845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6675, d82845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d6676 q = 2) : d82846 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6676, d82846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6676, d82846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d6677 q = 2) : d82847 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6677, d82847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6677, d82847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro4598 (p : Pattern) (selected : d6683 p = 2) : d82853 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d6557 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4574 q selected
  have h2 (q : Pattern) (selected : d6558 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d6558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d6566 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4574 q selected
    | true =>
      simp only [d6566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4576 q selected
  have h4 (q : Pattern) (selected : d6567 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d6567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d6568 q = 2) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d6568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d6568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d6619 q = 2) : d6566 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6619, d6566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4581 q selected
    | true =>
      simp only [d6619, d6566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4587 q selected
  have h7 (q : Pattern) (selected : d6626 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4588 q selected
    | true =>
      simp only [d6626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1070 q selected
  have h8 (q : Pattern) (selected : d6627 q = 2) : d6567 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6627, d6567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d6627, d6567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d6628 q = 2) : d82834 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d6628, d82834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d6628, d82834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d6629 q = 2) : d82835 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d6629, d82835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d6629, d82835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d6633 q = 2) : d82837 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6633, d82837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6633, d82837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4589 q selected
  have h12 (q : Pattern) (selected : d2326 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1072 q selected
  have h13 (q : Pattern) (selected : d6634 q = 2) : d82838 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6634, d82838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d6634, d82838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d6635 q = 2) : d82839 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d6635, d82839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d6635, d82839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d6636 q = 2) : d82840 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d6636, d82840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d6636, d82840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d6637 q = 2) : d82841 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d6637, d82841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d6637, d82841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d6678 q = 2) : d82848 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6678, d82848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6678, d82848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4597 q selected
  have h18 (q : Pattern) (selected : d2459 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1091 q selected
  have h19 (q : Pattern) (selected : d6679 q = 2) : d82849 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6679, d82849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d6679, d82849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d6680 q = 2) : d82850 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d6680, d82850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d6680, d82850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d6681 q = 2) : d82851 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d6681, d82851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d6681, d82851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d6682 q = 2) : d82852 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d6682, d82852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d6682, d82852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d6683 q = 2) : d82853 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d6683, d82853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d6683, d82853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro4599 (p : Pattern) (selected : d6689 p = 2) : d82859 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d6684 q = 2) : d82854 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d6684, d82854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6684, d82854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4598 q selected
  have h2 (q : Pattern) (selected : d6685 q = 2) : d82855 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d6685, d82855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6685, d82855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d6686 q = 2) : d82856 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d6686, d82856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6686, d82856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d6687 q = 2) : d82857 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d6687, d82857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6687, d82857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d6688 q = 2) : d82858 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d6688, d82858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6688, d82858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d6689 q = 2) : d82859 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d6689, d82859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6689, d82859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro4600 (p : Pattern) (selected : d6695 p = 2) : d82865 p = 1 := by
  have h0 (q : Pattern) (selected : d6114 q = 2) : d82746 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d6114, d82746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4469 q selected
    | true =>
      simp only [d6114, d82746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4492 q selected
  have h1 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h2 (q : Pattern) (selected : d6252 q = 2) : d82773 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d6252, d82773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d6252, d82773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4518 q selected
  have h3 (q : Pattern) (selected : d6253 q = 2) : d82774 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d6253, d82774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6253, d82774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d6397 q = 2) : d82801 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d6397, d82801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d6397, d82801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4545 q selected
  have h5 (q : Pattern) (selected : d6398 q = 2) : d82802 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d6398, d82802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d6398, d82802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d6399 q = 2) : d82803 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d6399, d82803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d6399, d82803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d6543 q = 2) : d82830 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d6543, d82830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d6543, d82830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4572 q selected
  have h8 (q : Pattern) (selected : d6544 q = 2) : d82831 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d6544, d82831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d6544, d82831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d6545 q = 2) : d82832 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d6545, d82832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d6545, d82832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d6546 q = 2) : d82833 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d6546, d82833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d6546, d82833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d6690 q = 2) : d82860 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d6690, d82860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d6690, d82860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4599 q selected
  have h12 (q : Pattern) (selected : d6691 q = 2) : d82861 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d6691, d82861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d6691, d82861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d6692 q = 2) : d82862 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d6692, d82862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d6692, d82862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d6693 q = 2) : d82863 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d6693, d82863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d6693, d82863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d6694 q = 2) : d82864 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d6694, d82864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d6694, d82864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d6695 q = 2) : d82865 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d6695, d82865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d6695, d82865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro4601 (p : Pattern) (selected : d6701 p = 2) : d82871 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d6696 q = 2) : d82866 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d6696, d82866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4600 q selected
    | true =>
      simp only [d6696, d82866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d6697 q = 2) : d82867 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d6697, d82867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d6697, d82867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d6698 q = 2) : d82868 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d6698, d82868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d6698, d82868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d6699 q = 2) : d82869 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d6699, d82869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d6699, d82869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d6700 q = 2) : d82870 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d6700, d82870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d6700, d82870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d6701 q = 2) : d82871 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d6701, d82871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d6701, d82871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4602 (p : Pattern) (selected : d6707 p = 2) : d82877 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d6702 q = 2) : d82872 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d6702, d82872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4601 q selected
    | true =>
      simp only [d6702, d82872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d6703 q = 2) : d82873 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d6703, d82873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d6703, d82873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d6704 q = 2) : d82874 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d6704, d82874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d6704, d82874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d6705 q = 2) : d82875 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d6705, d82875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d6705, d82875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d6706 q = 2) : d82876 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d6706, d82876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d6706, d82876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d6707 q = 2) : d82877 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d6707, d82877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d6707, d82877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4603 (p : Pattern) (selected : d6713 p = 2) : d82883 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d6708 q = 2) : d82878 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d6708, d82878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4602 q selected
    | true =>
      simp only [d6708, d82878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d6709 q = 2) : d82879 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d6709, d82879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d6709, d82879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d6710 q = 2) : d82880 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d6710, d82880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d6710, d82880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d6711 q = 2) : d82881 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d6711, d82881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d6711, d82881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d6712 q = 2) : d82882 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d6712, d82882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d6712, d82882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d6713 q = 2) : d82883 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d6713, d82883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d6713, d82883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4604 (p : Pattern) (selected : d6719 p = 2) : d82889 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d6714 q = 2) : d82884 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d6714, d82884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4603 q selected
    | true =>
      simp only [d6714, d82884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d6715 q = 2) : d82885 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d6715, d82885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d6715, d82885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d6716 q = 2) : d82886 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d6716, d82886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d6716, d82886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d6717 q = 2) : d82887 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d6717, d82887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d6717, d82887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d6718 q = 2) : d82888 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d6718, d82888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d6718, d82888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d6719 q = 2) : d82889 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d6719, d82889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d6719, d82889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4605 (p : Pattern) (selected : d6725 p = 2) : d82895 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d6720 q = 2) : d82890 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d6720, d82890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4604 q selected
    | true =>
      simp only [d6720, d82890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d6721 q = 2) : d82891 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d6721, d82891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d6721, d82891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d6722 q = 2) : d82892 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d6722, d82892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d6722, d82892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d6723 q = 2) : d82893 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d6723, d82893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d6723, d82893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d6724 q = 2) : d82894 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d6724, d82894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d6724, d82894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d6725 q = 2) : d82895 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d6725, d82895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d6725, d82895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4606 (p : Pattern) (selected : d6731 p = 2) : d82901 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d6726 q = 2) : d82896 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d6726, d82896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4605 q selected
    | true =>
      simp only [d6726, d82896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d6727 q = 2) : d82897 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d6727, d82897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d6727, d82897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d6728 q = 2) : d82898 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d6728, d82898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d6728, d82898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d6729 q = 2) : d82899 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d6729, d82899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d6729, d82899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d6730 q = 2) : d82900 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d6730, d82900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d6730, d82900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d6731 q = 2) : d82901 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d6731, d82901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d6731, d82901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4607 (p : Pattern) (selected : d6737 p = 2) : d82907 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d6732 q = 2) : d82902 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d6732, d82902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4606 q selected
    | true =>
      simp only [d6732, d82902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d6733 q = 2) : d82903 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d6733, d82903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d6733, d82903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d6734 q = 2) : d82904 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d6734, d82904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d6734, d82904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d6735 q = 2) : d82905 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d6735, d82905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d6735, d82905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d6736 q = 2) : d82906 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d6736, d82906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d6736, d82906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d6737 q = 2) : d82907 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d6737, d82907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d6737, d82907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4608 (p : Pattern) (selected : d82908 p = 0) : d83151 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d58784 q = 0) : d59229 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58784, d59229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58784, d59229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro190 q selected
  have h2 (q : Pattern) (selected : d58785 q = 0) : d59230 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58785, d59230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58785, d59230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d58786 q = 0) : d59231 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d58786, d59231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58786, d59231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d58787 q = 0) : d59232 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d58787, d59232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58787, d59232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d82908 q = 0) : d83151 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82908, d83151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d82908, d83151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro4609 (p : Pattern) (selected : d82913 p = 0) : d83156 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d82909 q = 0) : d83152 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82909, d83152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4608 q selected
    | true =>
      simp only [d82909, d83152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d82910 q = 0) : d83153 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82910, d83153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d82910, d83153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d82911 q = 0) : d83154 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82911, d83154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d82911, d83154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d82912 q = 0) : d83155 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82912, d83155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d82912, d83155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d82913 q = 0) : d83156 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d82913, d83156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d82913, d83156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro4610 (p : Pattern) (selected : d82923 p = 0) : d83166 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d82919 q = 0) : d83162 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82919, d83162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d82919, d83162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2763 q selected
  have h2 (q : Pattern) (selected : d82920 q = 0) : d83163 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82920, d83163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d82920, d83163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d82921 q = 0) : d83164 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82921, d83164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d82921, d83164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d82922 q = 0) : d83165 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82922, d83165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d82922, d83165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d58784 q = 0) : d59229 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58784, d59229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58784, d59229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro190 q selected
  have h6 (q : Pattern) (selected : d58785 q = 0) : d59230 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58785, d59230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d58785, d59230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d58786 q = 0) : d59231 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d58786, d59231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58786, d59231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d58787 q = 0) : d59232 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d58787, d59232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58787, d59232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d82923 q = 0) : d83166 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82923, d83166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d82923, d83166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro4611 (p : Pattern) (selected : d82927 p = 0) : d83170 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d58790 q = 0) : d59235 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58790, d59235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58790, d59235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro192 q selected
  have h2 (q : Pattern) (selected : d58791 q = 0) : d59236 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58791, d59236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58791, d59236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d58792 q = 0) : d59237 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d58792, d59237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58792, d59237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d58793 q = 0) : d59238 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d58793, d59238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58793, d59238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d82927 q = 0) : d83170 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82927, d83170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d82927, d83170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro4612 (p : Pattern) (selected : d82936 p = 0) : d83179 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d82932 q = 0) : d83175 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82932, d83175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d82932, d83175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro197 q selected
  have h2 (q : Pattern) (selected : d82933 q = 0) : d83176 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82933, d83176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d82933, d83176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d82934 q = 0) : d83177 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82934, d83177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d82934, d83177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d82935 q = 0) : d83178 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82935, d83178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d82935, d83178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d82936 q = 0) : d83179 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82936, d83179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d82936, d83179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro4613 (p : Pattern) (selected : d82941 p = 0) : d83184 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d82924 q = 0) : d83167 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82924, d83167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4610 q selected
    | true =>
      simp only [d82924, d83167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1794 q selected
  have h2 (q : Pattern) (selected : d82925 q = 0) : d83168 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82925, d83168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d82925, d83168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d82926 q = 0) : d83169 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82926, d83169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d82926, d83169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d82928 q = 0) : d83171 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82928, d83171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d82928, d83171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4611 q selected
  have h5 (q : Pattern) (selected : d82929 q = 0) : d83172 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82929, d83172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d82929, d83172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d82930 q = 0) : d83173 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82930, d83173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d82930, d83173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d82931 q = 0) : d83174 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82931, d83174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d82931, d83174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d82937 q = 0) : d83180 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82937, d83180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d82937, d83180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4612 q selected
  have h9 (q : Pattern) (selected : d82938 q = 0) : d83181 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82938, d83181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d82938, d83181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d82939 q = 0) : d83182 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82939, d83182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d82939, d83182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d82940 q = 0) : d83183 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82940, d83183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d82940, d83183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d82941 q = 0) : d83184 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d82941, d83184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d82941, d83184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  exact h12 p selected
theorem eqIntro4614 (p : Pattern) (selected : d82947 p = 0) : d83190 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d82914 q = 0) : d83157 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d82914, d83157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d82914, d83157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4609 q selected
  have h2 (q : Pattern) (selected : d82915 q = 0) : d83158 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d82915, d83158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d82915, d83158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d82916 q = 0) : d83159 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d82916, d83159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d82916, d83159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d82917 q = 0) : d83160 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d82917, d83160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d82917, d83160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d82918 q = 0) : d83161 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d82918, d83161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d82918, d83161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d82942 q = 0) : d83185 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d82942, d83185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d82942, d83185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4613 q selected
  have h7 (q : Pattern) (selected : d82943 q = 0) : d83186 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d82943, d83186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d82943, d83186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d82944 q = 0) : d83187 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d82944, d83187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d82944, d83187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d82945 q = 0) : d83188 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d82945, d83188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d82945, d83188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d82946 q = 0) : d83189 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d82946, d83189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d82946, d83189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d82947 q = 0) : d83190 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d82947, d83190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d82947, d83190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro4615 (p : Pattern) (selected : d82952 p = 0) : d83195 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d82948 q = 0) : d83191 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82948, d83191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d82948, d83191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2775 q selected
  have h2 (q : Pattern) (selected : d82949 q = 0) : d83192 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82949, d83192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d82949, d83192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d82950 q = 0) : d83193 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82950, d83193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d82950, d83193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d82951 q = 0) : d83194 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82951, d83194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d82951, d83194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d58843 q = 0) : d59288 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58843, d59288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58843, d59288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro266 q selected
  have h6 (q : Pattern) (selected : d58844 q = 0) : d59289 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58844, d59289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d58844, d59289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d58845 q = 0) : d59290 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d58845, d59290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58845, d59290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d58846 q = 0) : d59291 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d58846, d59291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58846, d59291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d82952 q = 0) : d83195 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82952, d83195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d82952, d83195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro4616 (p : Pattern) (selected : d82956 p = 0) : d83199 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d58849 q = 0) : d59294 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58849, d59294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58849, d59294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro269 q selected
  have h2 (q : Pattern) (selected : d58850 q = 0) : d59295 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58850, d59295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58850, d59295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d58851 q = 0) : d59296 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d58851, d59296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58851, d59296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d58852 q = 0) : d59297 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d58852, d59297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58852, d59297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d82956 q = 0) : d83199 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82956, d83199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d82956, d83199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro4617 (p : Pattern) (selected : d82965 p = 0) : d83208 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d82961 q = 0) : d83204 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82961, d83204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d82961, d83204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro313 q selected
  have h2 (q : Pattern) (selected : d82962 q = 0) : d83205 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82962, d83205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d82962, d83205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d82963 q = 0) : d83206 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82963, d83206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d82963, d83206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d82964 q = 0) : d83207 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82964, d83207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d82964, d83207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d82965 q = 0) : d83208 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82965, d83208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d82965, d83208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro4618 (p : Pattern) (selected : d82970 p = 0) : d83213 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d82953 q = 0) : d83196 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82953, d83196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4615 q selected
    | true =>
      simp only [d82953, d83196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1802 q selected
  have h2 (q : Pattern) (selected : d82954 q = 0) : d83197 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82954, d83197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d82954, d83197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d82955 q = 0) : d83198 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82955, d83198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d82955, d83198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d82957 q = 0) : d83200 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82957, d83200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d82957, d83200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4616 q selected
  have h5 (q : Pattern) (selected : d82958 q = 0) : d83201 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82958, d83201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d82958, d83201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d82959 q = 0) : d83202 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82959, d83202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d82959, d83202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d82960 q = 0) : d83203 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82960, d83203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d82960, d83203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d82966 q = 0) : d83209 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82966, d83209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d82966, d83209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4617 q selected
  have h9 (q : Pattern) (selected : d82967 q = 0) : d83210 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82967, d83210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d82967, d83210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d82968 q = 0) : d83211 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82968, d83211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d82968, d83211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d82969 q = 0) : d83212 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82969, d83212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d82969, d83212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d82970 q = 0) : d83213 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d82970, d83213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d82970, d83213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  exact h12 p selected
theorem eqIntro4619 (p : Pattern) (selected : d82976 p = 0) : d83219 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d82971 q = 0) : d83214 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d82971, d83214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d82971, d83214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4618 q selected
  have h2 (q : Pattern) (selected : d82972 q = 0) : d83215 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d82972, d83215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d82972, d83215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d82973 q = 0) : d83216 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d82973, d83216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d82973, d83216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d82974 q = 0) : d83217 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d82974, d83217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d82974, d83217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d82975 q = 0) : d83218 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d82975, d83218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d82975, d83218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d82976 q = 0) : d83219 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d82976, d83219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d82976, d83219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro4620 (p : Pattern) (selected : d82982 p = 0) : d83225 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d82978 q = 0) : d83221 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82978, d83221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d82978, d83221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2787 q selected
  have h2 (q : Pattern) (selected : d82979 q = 0) : d83222 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82979, d83222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d82979, d83222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d82980 q = 0) : d83223 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82980, d83223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d82980, d83223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d82981 q = 0) : d83224 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82981, d83224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d82981, d83224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d58903 q = 0) : d59348 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58903, d59348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58903, d59348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro324 q selected
  have h6 (q : Pattern) (selected : d58904 q = 0) : d59349 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58904, d59349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d58904, d59349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d58905 q = 0) : d59350 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d58905, d59350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58905, d59350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d58906 q = 0) : d59351 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d58906, d59351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58906, d59351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d82982 q = 0) : d83225 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82982, d83225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d82982, d83225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro4621 (p : Pattern) (selected : d82986 p = 0) : d83229 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d58909 q = 0) : d59354 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58909, d59354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58909, d59354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro327 q selected
  have h2 (q : Pattern) (selected : d58910 q = 0) : d59355 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58910, d59355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58910, d59355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d58911 q = 0) : d59356 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d58911, d59356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58911, d59356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d58912 q = 0) : d59357 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d58912, d59357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58912, d59357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d82986 q = 0) : d83229 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82986, d83229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d82986, d83229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro4622 (p : Pattern) (selected : d82995 p = 0) : d83238 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d82991 q = 0) : d83234 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82991, d83234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d82991, d83234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro380 q selected
  have h2 (q : Pattern) (selected : d82992 q = 0) : d83235 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82992, d83235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d82992, d83235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d82993 q = 0) : d83236 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82993, d83236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d82993, d83236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d82994 q = 0) : d83237 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82994, d83237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d82994, d83237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d82995 q = 0) : d83238 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82995, d83238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d82995, d83238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro4623 (p : Pattern) (selected : d83000 p = 0) : d83243 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d82983 q = 0) : d83226 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82983, d83226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4620 q selected
    | true =>
      simp only [d82983, d83226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1810 q selected
  have h2 (q : Pattern) (selected : d82984 q = 0) : d83227 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82984, d83227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d82984, d83227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d82985 q = 0) : d83228 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82985, d83228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d82985, d83228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d82987 q = 0) : d83230 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82987, d83230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d82987, d83230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4621 q selected
  have h5 (q : Pattern) (selected : d82988 q = 0) : d83231 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82988, d83231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d82988, d83231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d82989 q = 0) : d83232 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82989, d83232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d82989, d83232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d82990 q = 0) : d83233 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82990, d83233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d82990, d83233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d82996 q = 0) : d83239 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82996, d83239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d82996, d83239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4622 q selected
  have h9 (q : Pattern) (selected : d82997 q = 0) : d83240 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82997, d83240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d82997, d83240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d82998 q = 0) : d83241 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82998, d83241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d82998, d83241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d82999 q = 0) : d83242 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82999, d83242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d82999, d83242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d83000 q = 0) : d83243 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d83000, d83243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d83000, d83243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  exact h12 p selected
theorem eqIntro4624 (p : Pattern) (selected : d83006 p = 0) : d83249 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d83001 q = 0) : d83244 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d83001, d83244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d83001, d83244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4623 q selected
  have h2 (q : Pattern) (selected : d83002 q = 0) : d83245 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d83002, d83245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d83002, d83245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d83003 q = 0) : d83246 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d83003, d83246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d83003, d83246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d83004 q = 0) : d83247 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d83004, d83247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d83004, d83247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d83005 q = 0) : d83248 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d83005, d83248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d83005, d83248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d83006 q = 0) : d83249 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d83006, d83249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d83006, d83249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro4625 (p : Pattern) (selected : d83013 p = 0) : d83256 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d83009 q = 0) : d83252 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83009, d83252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d83009, d83252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2802 q selected
  have h2 (q : Pattern) (selected : d83010 q = 0) : d83253 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83010, d83253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d83010, d83253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d83011 q = 0) : d83254 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83011, d83254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d83011, d83254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d83012 q = 0) : d83255 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83012, d83255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d83012, d83255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d58964 q = 0) : d59409 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58964, d59409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58964, d59409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro396 q selected
  have h6 (q : Pattern) (selected : d58965 q = 0) : d59410 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58965, d59410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d58965, d59410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d58966 q = 0) : d59411 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d58966, d59411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58966, d59411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d58967 q = 0) : d59412 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d58967, d59412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58967, d59412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d83013 q = 0) : d83256 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83013, d83256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d83013, d83256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro4626 (p : Pattern) (selected : d83017 p = 0) : d83260 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d58970 q = 0) : d59415 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58970, d59415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58970, d59415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro399 q selected
  have h2 (q : Pattern) (selected : d58971 q = 0) : d59416 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58971, d59416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58971, d59416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d58972 q = 0) : d59417 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d58972, d59417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58972, d59417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d58973 q = 0) : d59418 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d58973, d59418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58973, d59418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d83017 q = 0) : d83260 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83017, d83260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d83017, d83260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro4627 (p : Pattern) (selected : d83026 p = 0) : d83269 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d83022 q = 0) : d83265 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83022, d83265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d83022, d83265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro456 q selected
  have h2 (q : Pattern) (selected : d83023 q = 0) : d83266 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83023, d83266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d83023, d83266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d83024 q = 0) : d83267 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83024, d83267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d83024, d83267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d83025 q = 0) : d83268 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83025, d83268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d83025, d83268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d83026 q = 0) : d83269 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83026, d83269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d83026, d83269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro4628 (p : Pattern) (selected : d83031 p = 0) : d83274 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d83014 q = 0) : d83257 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83014, d83257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4625 q selected
    | true =>
      simp only [d83014, d83257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1818 q selected
  have h2 (q : Pattern) (selected : d83015 q = 0) : d83258 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83015, d83258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d83015, d83258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d83016 q = 0) : d83259 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d83016, d83259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d83016, d83259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d83018 q = 0) : d83261 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83018, d83261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d83018, d83261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4626 q selected
  have h5 (q : Pattern) (selected : d83019 q = 0) : d83262 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83019, d83262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d83019, d83262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d83020 q = 0) : d83263 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d83020, d83263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d83020, d83263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d83021 q = 0) : d83264 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d83021, d83264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d83021, d83264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d83027 q = 0) : d83270 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83027, d83270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d83027, d83270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4627 q selected
  have h9 (q : Pattern) (selected : d83028 q = 0) : d83271 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83028, d83271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d83028, d83271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d83029 q = 0) : d83272 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d83029, d83272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d83029, d83272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d83030 q = 0) : d83273 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d83030, d83273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d83030, d83273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d83031 q = 0) : d83274 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d83031, d83274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d83031, d83274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  exact h12 p selected
theorem eqIntro4629 (p : Pattern) (selected : d83037 p = 0) : d83280 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d83032 q = 0) : d83275 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d83032, d83275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d83032, d83275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4628 q selected
  have h2 (q : Pattern) (selected : d83033 q = 0) : d83276 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d83033, d83276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d83033, d83276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d83034 q = 0) : d83277 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d83034, d83277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d83034, d83277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d83035 q = 0) : d83278 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d83035, d83278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d83035, d83278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d83036 q = 0) : d83279 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d83036, d83279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d83036, d83279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d83037 q = 0) : d83280 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d83037, d83280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d83037, d83280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro4630 (p : Pattern) (selected : d83045 p = 0) : d83288 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d83041 q = 0) : d83284 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83041, d83284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d83041, d83284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2817 q selected
  have h2 (q : Pattern) (selected : d83042 q = 0) : d83285 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83042, d83285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d83042, d83285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d83043 q = 0) : d83286 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83043, d83286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d83043, d83286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d83044 q = 0) : d83287 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83044, d83287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d83044, d83287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d59026 q = 0) : d59471 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d59026, d59471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59026, d59471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro478 q selected
  have h6 (q : Pattern) (selected : d59027 q = 0) : d59472 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d59027, d59472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d59027, d59472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d59028 q = 0) : d59473 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d59028, d59473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59028, d59473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d59029 q = 0) : d59474 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d59029, d59474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59029, d59474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d83045 q = 0) : d83288 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83045, d83288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d83045, d83288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro4631 (p : Pattern) (selected : d83049 p = 0) : d83292 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d59032 q = 0) : d59477 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d59032, d59477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59032, d59477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro481 q selected
  have h2 (q : Pattern) (selected : d59033 q = 0) : d59478 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d59033, d59478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d59033, d59478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d59034 q = 0) : d59479 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d59034, d59479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59034, d59479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d59035 q = 0) : d59480 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d59035, d59480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59035, d59480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d83049 q = 0) : d83292 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83049, d83292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d83049, d83292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro4632 (p : Pattern) (selected : d83058 p = 0) : d83301 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d83054 q = 0) : d83297 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83054, d83297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d83054, d83297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro542 q selected
  have h2 (q : Pattern) (selected : d83055 q = 0) : d83298 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83055, d83298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d83055, d83298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d83056 q = 0) : d83299 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83056, d83299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d83056, d83299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d83057 q = 0) : d83300 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83057, d83300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d83057, d83300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d83058 q = 0) : d83301 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83058, d83301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d83058, d83301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro4633 (p : Pattern) (selected : d83063 p = 0) : d83306 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d83046 q = 0) : d83289 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83046, d83289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4630 q selected
    | true =>
      simp only [d83046, d83289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1826 q selected
  have h2 (q : Pattern) (selected : d83047 q = 0) : d83290 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83047, d83290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d83047, d83290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d83048 q = 0) : d83291 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d83048, d83291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d83048, d83291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d83050 q = 0) : d83293 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83050, d83293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d83050, d83293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4631 q selected
  have h5 (q : Pattern) (selected : d83051 q = 0) : d83294 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83051, d83294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d83051, d83294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d83052 q = 0) : d83295 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d83052, d83295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d83052, d83295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d83053 q = 0) : d83296 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d83053, d83296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d83053, d83296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d83059 q = 0) : d83302 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83059, d83302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d83059, d83302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4632 q selected
  have h9 (q : Pattern) (selected : d83060 q = 0) : d83303 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83060, d83303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d83060, d83303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d83061 q = 0) : d83304 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d83061, d83304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d83061, d83304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d83062 q = 0) : d83305 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d83062, d83305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d83062, d83305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d83063 q = 0) : d83306 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d83063, d83306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d83063, d83306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  exact h12 p selected
theorem eqIntro4634 (p : Pattern) (selected : d83069 p = 0) : d83312 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d83064 q = 0) : d83307 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d83064, d83307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d83064, d83307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4633 q selected
  have h2 (q : Pattern) (selected : d83065 q = 0) : d83308 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d83065, d83308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d83065, d83308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d83066 q = 0) : d83309 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d83066, d83309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d83066, d83309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d83067 q = 0) : d83310 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d83067, d83310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d83067, d83310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d83068 q = 0) : d83311 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d83068, d83311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d83068, d83311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d83069 q = 0) : d83312 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d83069, d83312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d83069, d83312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro4635 (p : Pattern) (selected : d83078 p = 0) : d83321 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d83074 q = 0) : d83317 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83074, d83317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d83074, d83317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2831 q selected
  have h2 (q : Pattern) (selected : d83075 q = 0) : d83318 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83075, d83318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d83075, d83318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d83076 q = 0) : d83319 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83076, d83319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d83076, d83319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d83077 q = 0) : d83320 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83077, d83320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d83077, d83320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d59089 q = 0) : d59534 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d59089, d59534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59089, d59534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro567 q selected
  have h6 (q : Pattern) (selected : d59090 q = 0) : d59535 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d59090, d59535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d59090, d59535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d59091 q = 0) : d59536 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d59091, d59536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59091, d59536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d59092 q = 0) : d59537 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d59092, d59537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59092, d59537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d83078 q = 0) : d83321 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83078, d83321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d83078, d83321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro4636 (p : Pattern) (selected : d83082 p = 0) : d83325 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d59095 q = 0) : d59540 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d59095, d59540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59095, d59540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro570 q selected
  have h2 (q : Pattern) (selected : d59096 q = 0) : d59541 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d59096, d59541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d59096, d59541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d59097 q = 0) : d59542 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d59097, d59542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59097, d59542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d59098 q = 0) : d59543 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d59098, d59543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59098, d59543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d83082 q = 0) : d83325 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83082, d83325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d83082, d83325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro4637 (p : Pattern) (selected : d83091 p = 0) : d83334 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d83087 q = 0) : d83330 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83087, d83330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d83087, d83330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro632 q selected
  have h2 (q : Pattern) (selected : d83088 q = 0) : d83331 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83088, d83331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d83088, d83331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d83089 q = 0) : d83332 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83089, d83332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d83089, d83332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d83090 q = 0) : d83333 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83090, d83333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d83090, d83333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d83091 q = 0) : d83334 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83091, d83334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d83091, d83334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro4638 (p : Pattern) (selected : d83096 p = 0) : d83339 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d83079 q = 0) : d83322 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83079, d83322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4635 q selected
    | true =>
      simp only [d83079, d83322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1834 q selected
  have h2 (q : Pattern) (selected : d83080 q = 0) : d83323 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83080, d83323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d83080, d83323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d83081 q = 0) : d83324 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d83081, d83324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d83081, d83324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d83083 q = 0) : d83326 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83083, d83326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d83083, d83326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4636 q selected
  have h5 (q : Pattern) (selected : d83084 q = 0) : d83327 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83084, d83327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d83084, d83327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d83085 q = 0) : d83328 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d83085, d83328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d83085, d83328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d83086 q = 0) : d83329 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d83086, d83329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d83086, d83329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d83092 q = 0) : d83335 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83092, d83335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d83092, d83335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4637 q selected
  have h9 (q : Pattern) (selected : d83093 q = 0) : d83336 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83093, d83336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d83093, d83336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d83094 q = 0) : d83337 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d83094, d83337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d83094, d83337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d83095 q = 0) : d83338 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d83095, d83338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d83095, d83338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d83096 q = 0) : d83339 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d83096, d83339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d83096, d83339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  exact h12 p selected
theorem eqIntro4639 (p : Pattern) (selected : d83102 p = 0) : d83345 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d83097 q = 0) : d83340 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d83097, d83340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d83097, d83340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4638 q selected
  have h2 (q : Pattern) (selected : d83098 q = 0) : d83341 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d83098, d83341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d83098, d83341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d83099 q = 0) : d83342 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d83099, d83342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d83099, d83342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d83100 q = 0) : d83343 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d83100, d83343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d83100, d83343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d83101 q = 0) : d83344 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d83101, d83344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d83101, d83344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d83102 q = 0) : d83345 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d83102, d83345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d83102, d83345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro4640 (p : Pattern) (selected : d83108 p = 0) : d83351 p = 1 := by
  have h0 (q : Pattern) (selected : d82977 q = 0) : d83220 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d82977, d83220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4614 q selected
    | true =>
      simp only [d82977, d83220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4619 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d83007 q = 0) : d83250 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d83007, d83250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d83007, d83250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4624 q selected
  have h3 (q : Pattern) (selected : d83008 q = 0) : d83251 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d83008, d83251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d83008, d83251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d83038 q = 0) : d83281 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d83038, d83281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d83038, d83281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4629 q selected
  have h5 (q : Pattern) (selected : d83039 q = 0) : d83282 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d83039, d83282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d83039, d83282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d83040 q = 0) : d83283 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d83040, d83283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d83040, d83283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d83070 q = 0) : d83313 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d83070, d83313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d83070, d83313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4634 q selected
  have h8 (q : Pattern) (selected : d83071 q = 0) : d83314 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d83071, d83314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d83071, d83314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d83072 q = 0) : d83315 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d83072, d83315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d83072, d83315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d83073 q = 0) : d83316 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d83073, d83316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d83073, d83316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d83103 q = 0) : d83346 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d83103, d83346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d83103, d83346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4639 q selected
  have h12 (q : Pattern) (selected : d83104 q = 0) : d83347 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d83104, d83347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d83104, d83347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d83105 q = 0) : d83348 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d83105, d83348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d83105, d83348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d83106 q = 0) : d83349 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d83106, d83349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d83106, d83349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d83107 q = 0) : d83350 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d83107, d83350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d83107, d83350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d83108 q = 0) : d83351 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d83108, d83351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d83108, d83351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro4641 (p : Pattern) (selected : d83114 p = 0) : d83357 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d83109 q = 0) : d83352 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d83109, d83352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4640 q selected
    | true =>
      simp only [d83109, d83352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d83110 q = 0) : d83353 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d83110, d83353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d83110, d83353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d83111 q = 0) : d83354 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d83111, d83354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d83111, d83354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d83112 q = 0) : d83355 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d83112, d83355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d83112, d83355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d83113 q = 0) : d83356 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d83113, d83356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d83113, d83356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d83114 q = 0) : d83357 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d83114, d83357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d83114, d83357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4642 (p : Pattern) (selected : d83120 p = 0) : d83363 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d83115 q = 0) : d83358 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d83115, d83358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4641 q selected
    | true =>
      simp only [d83115, d83358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d83116 q = 0) : d83359 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d83116, d83359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d83116, d83359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d83117 q = 0) : d83360 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d83117, d83360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d83117, d83360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d83118 q = 0) : d83361 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d83118, d83361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d83118, d83361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d83119 q = 0) : d83362 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d83119, d83362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d83119, d83362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d83120 q = 0) : d83363 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d83120, d83363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d83120, d83363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4643 (p : Pattern) (selected : d83126 p = 0) : d83369 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d83121 q = 0) : d83364 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d83121, d83364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4642 q selected
    | true =>
      simp only [d83121, d83364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d83122 q = 0) : d83365 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d83122, d83365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d83122, d83365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d83123 q = 0) : d83366 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d83123, d83366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d83123, d83366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d83124 q = 0) : d83367 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d83124, d83367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d83124, d83367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d83125 q = 0) : d83368 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d83125, d83368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d83125, d83368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d83126 q = 0) : d83369 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d83126, d83369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d83126, d83369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4644 (p : Pattern) (selected : d83132 p = 0) : d83375 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d83127 q = 0) : d83370 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d83127, d83370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4643 q selected
    | true =>
      simp only [d83127, d83370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d83128 q = 0) : d83371 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d83128, d83371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d83128, d83371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d83129 q = 0) : d83372 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d83129, d83372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d83129, d83372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d83130 q = 0) : d83373 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d83130, d83373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d83130, d83373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d83131 q = 0) : d83374 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d83131, d83374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d83131, d83374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d83132 q = 0) : d83375 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d83132, d83375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d83132, d83375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4645 (p : Pattern) (selected : d83138 p = 0) : d83381 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d83133 q = 0) : d83376 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d83133, d83376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4644 q selected
    | true =>
      simp only [d83133, d83376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d83134 q = 0) : d83377 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d83134, d83377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d83134, d83377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d83135 q = 0) : d83378 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d83135, d83378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d83135, d83378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d83136 q = 0) : d83379 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d83136, d83379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d83136, d83379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d83137 q = 0) : d83380 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d83137, d83380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d83137, d83380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d83138 q = 0) : d83381 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d83138, d83381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d83138, d83381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4646 (p : Pattern) (selected : d83144 p = 0) : d83387 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d83139 q = 0) : d83382 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d83139, d83382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4645 q selected
    | true =>
      simp only [d83139, d83382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d83140 q = 0) : d83383 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d83140, d83383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d83140, d83383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d83141 q = 0) : d83384 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d83141, d83384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d83141, d83384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d83142 q = 0) : d83385 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d83142, d83385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d83142, d83385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d83143 q = 0) : d83386 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d83143, d83386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d83143, d83386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d83144 q = 0) : d83387 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d83144, d83387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d83144, d83387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4647 (p : Pattern) (selected : d83150 p = 0) : d83393 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d83145 q = 0) : d83388 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d83145, d83388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4646 q selected
    | true =>
      simp only [d83145, d83388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d83146 q = 0) : d83389 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d83146, d83389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d83146, d83389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d83147 q = 0) : d83390 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d83147, d83390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d83147, d83390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d83148 q = 0) : d83391 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d83148, d83391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d83148, d83391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d83149 q = 0) : d83392 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d83149, d83392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d83149, d83392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d83150 q = 0) : d83393 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d83150, d83393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d83150, d83393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4648 (p : Pattern) (selected : d83150 p = 1) : d83150 p = 1 := by
  have h0 (q : Pattern) (selected : d83150 q = 1) : d83150 q = 1 := by
    exact selected
  exact h0 p selected
theorem eqIntro4649 (p : Pattern) (selected : d7241 p = 0) : d83664 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d145 q = 0) : d51996 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d51996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro206 q selected
    | true =>
      simp only [d145, d51996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro188 q selected
  have h2 (q : Pattern) (selected : d146 q = 0) : d51997 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d51997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d146, d51997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d147 q = 0) : d51998 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d51998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d147, d51998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d31 q = 0) : d51883 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, d51883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro188 q selected
    | true =>
      simp only [d31, d51883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d32 q = 0) : d51884 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, d51884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32, d51884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d33 q = 0) : d51885 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, d51885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d33, d51885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d148 q = 0) : d51999 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148, d51999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d148, d51999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7240 q = 0) : d83663 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7240, d83663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7240, d83663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d7241 q = 0) : d83664 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7241, d83664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7241, d83664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro4650 (p : Pattern) (selected : d7247 p = 0) : d83670 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7242 q = 0) : d83665 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, d83665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4649 q selected
    | true =>
      simp only [d7242, d83665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7243 q = 0) : d83666 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, d83666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7243, d83666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d37 q = 0) : d51889 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro189 q selected
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d38 q = 0) : d51890 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7244 q = 0) : d83667 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7244, d83667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7244, d83667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7245 q = 0) : d83668 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7245, d83668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7245, d83668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7246 q = 0) : d83669 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7246, d83669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7246, d83669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7247 q = 0) : d83670 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7247, d83670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7247, d83670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro4651 (p : Pattern) (selected : d7253 p = 0) : d83676 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117 q = 0) : d51969 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, d51969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro202 q selected
    | true =>
      simp only [d117, d51969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118 q = 0) : d51970 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, d51970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118, d51970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d119 q = 0) : d51971 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, d51971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d119, d51971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d120 q = 0) : d51972 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, d51972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d120, d51972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d124 q = 0) : d51976 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, d51976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro203 q selected
    | true =>
      simp only [d124, d51976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d125 q = 0) : d51977 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, d51977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d125, d51977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d126 q = 0) : d51978 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, d51978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d126, d51978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7248 q = 0) : d83671 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7248, d83671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4650 q selected
    | true =>
      simp only [d7248, d83671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro190 q selected
  have h9 (q : Pattern) (selected : d188 q = 0) : d51895 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d188, d51895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro213 q selected
    | true =>
      simp only [d188, d51895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d7249 q = 0) : d83672 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7249, d83672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7249, d83672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d43 q = 0) : d51895 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro190 q selected
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d44 q = 0) : d51896 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d7250 q = 0) : d83673 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7250, d83673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d7250, d83673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d7251 q = 0) : d83674 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7251, d83674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7251, d83674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d7252 q = 0) : d83675 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7252, d83675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7252, d83675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d7253 q = 0) : d83676 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7253, d83676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7253, d83676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro4652 (p : Pattern) (selected : d7254 p = 0) : d83677 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7242 q = 0) : d83665 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, d83665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4649 q selected
    | true =>
      simp only [d7242, d83665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7243 q = 0) : d83666 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, d83666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7243, d83666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d37 q = 0) : d51889 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro189 q selected
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d38 q = 0) : d51890 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7244 q = 0) : d83667 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7244, d83667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7244, d83667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7245 q = 0) : d83668 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7245, d83668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7245, d83668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7246 q = 0) : d83669 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7246, d83669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7246, d83669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7254 q = 0) : d83677 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7254, d83677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7254, d83677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro4653 (p : Pattern) (selected : d7260 p = 0) : d83683 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117 q = 0) : d51969 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, d51969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro202 q selected
    | true =>
      simp only [d117, d51969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118 q = 0) : d51970 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, d51970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118, d51970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d119 q = 0) : d51971 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, d51971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d119, d51971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d120 q = 0) : d51972 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, d51972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d120, d51972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d124 q = 0) : d51976 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, d51976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro203 q selected
    | true =>
      simp only [d124, d51976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d125 q = 0) : d51977 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, d51977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d125, d51977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d126 q = 0) : d51978 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, d51978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d126, d51978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7248 q = 0) : d83671 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7248, d83671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4650 q selected
    | true =>
      simp only [d7248, d83671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro190 q selected
  have h9 (q : Pattern) (selected : d188 q = 0) : d51895 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d188, d51895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro213 q selected
    | true =>
      simp only [d188, d51895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d7249 q = 0) : d83672 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7249, d83672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7249, d83672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d43 q = 0) : d51895 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro190 q selected
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d44 q = 0) : d51896 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d7250 q = 0) : d83673 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7250, d83673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d7250, d83673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d7251 q = 0) : d83674 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7251, d83674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7251, d83674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d7252 q = 0) : d83675 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7252, d83675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7252, d83675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d195 q = 0) : d52015 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195, d52015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro215 q selected
    | true =>
      simp only [d195, d52015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d196 q = 0) : d52016 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d196, d52016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d196, d52016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d197 q = 0) : d52017 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d197, d52017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d197, d52017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d198 q = 0) : d52018 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198, d52018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d198, d52018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d200 q = 0) : d52020 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d200, d52020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro216 q selected
    | true =>
      simp only [d200, d52020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d201 q = 0) : d52021 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201, d52021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d201, d52021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d202 q = 0) : d52022 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202, d52022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d202, d52022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d7255 q = 0) : d83678 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7255, d83678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4652 q selected
    | true =>
      simp only [d7255, d83678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro192 q selected
  have h24 (q : Pattern) (selected : d206 q = 0) : d51902 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d206, d51902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro218 q selected
    | true =>
      simp only [d206, d51902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h25 (q : Pattern) (selected : d7256 q = 0) : d83679 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7256, d83679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d7256, d83679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d50 q = 0) : d51902 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro192 q selected
    | true =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d51 q = 0) : d51903 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d7257 q = 0) : d83680 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7257, d83680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d7257, d83680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d7258 q = 0) : d83681 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7258, d83681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d7258, d83681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d7259 q = 0) : d83682 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7259, d83682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d7259, d83682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d7260 q = 0) : d83683 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7260, d83683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d7260, d83683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro4654 (p : Pattern) (selected : d7267 p = 0) : d83690 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7255 q = 0) : d83678 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7255, d83678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4652 q selected
    | true =>
      simp only [d7255, d83678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro192 q selected
  have h2 (q : Pattern) (selected : d206 q = 0) : d51902 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d206, d51902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro218 q selected
    | true =>
      simp only [d206, d51902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d7256 q = 0) : d83679 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7256, d83679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d7256, d83679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d50 q = 0) : d51902 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro192 q selected
    | true =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d51 q = 0) : d51903 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d7257 q = 0) : d83680 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7257, d83680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7257, d83680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7265 q = 0) : d83688 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7265, d83688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7265, d83688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7266 q = 0) : d83689 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7266, d83689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7266, d83689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d7267 q = 0) : d83690 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7267, d83690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7267, d83690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro4655 (p : Pattern) (selected : d7274 p = 0) : d83697 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232 q = 0) : d52050 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d52050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro222 q selected
    | true =>
      simp only [d232, d52050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro195 q selected
  have h2 (q : Pattern) (selected : d233 q = 0) : d52051 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d52051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233, d52051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d234 q = 0) : d52052 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d52052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d234, d52052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d72 q = 0) : d51924 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, d51924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro195 q selected
    | true =>
      simp only [d72, d51924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d73 q = 0) : d51925 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, d51925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d73, d51925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d74 q = 0) : d51926 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, d51926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d74, d51926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d235 q = 0) : d52053 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d235, d52053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d235, d52053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7273 q = 0) : d83696 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7273, d83696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7273, d83696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d7274 q = 0) : d83697 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7274, d83697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7274, d83697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro4656 (p : Pattern) (selected : d7280 p = 0) : d83703 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7275 q = 0) : d83698 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7275, d83698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4655 q selected
    | true =>
      simp only [d7275, d83698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7276 q = 0) : d83699 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7276, d83699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7276, d83699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d78 q = 0) : d51930 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78, d51930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro196 q selected
    | true =>
      simp only [d78, d51930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d79 q = 0) : d51931 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79, d51931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d79, d51931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7277 q = 0) : d83700 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7277, d83700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7277, d83700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7278 q = 0) : d83701 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7278, d83701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7278, d83701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7279 q = 0) : d83702 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7279, d83702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7279, d83702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7280 q = 0) : d83703 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7280, d83703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7280, d83703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro4657 (p : Pattern) (selected : d7286 p = 0) : d83709 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7281 q = 0) : d83704 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7281, d83704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4656 q selected
    | true =>
      simp only [d7281, d83704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro197 q selected
  have h2 (q : Pattern) (selected : d263 q = 0) : d51936 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263, d51936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro227 q selected
    | true =>
      simp only [d263, d51936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d7282 q = 0) : d83705 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7282, d83705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d7282, d83705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d84 q = 0) : d51936 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, d51936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro197 q selected
    | true =>
      simp only [d84, d51936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d85 q = 0) : d51937 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85, d51937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d85, d51937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d7283 q = 0) : d83706 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7283, d83706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7283, d83706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7284 q = 0) : d83707 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7284, d83707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7284, d83707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7285 q = 0) : d83708 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7285, d83708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7285, d83708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d7286 q = 0) : d83709 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7286, d83709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7286, d83709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro4658 (p : Pattern) (selected : d7292 p = 0) : d83715 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d105 q = 0) : d51957 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105, d51957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105, d51957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro200 q selected
  have h2 (q : Pattern) (selected : d106 q = 0) : d51958 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d106, d51958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d106, d51958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d112 q = 0) : d51964 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, d51964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro200 q selected
    | true =>
      simp only [d112, d51964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro201 q selected
  have h4 (q : Pattern) (selected : d113 q = 0) : d51965 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, d51965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d113, d51965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d114 q = 0) : d51966 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d114, d51966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d114, d51966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7261 q = 0) : d83684 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7261, d83684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4651 q selected
    | true =>
      simp only [d7261, d83684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4653 q selected
  have h7 (q : Pattern) (selected : d214 q = 0) : d52032 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214, d52032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro220 q selected
    | true =>
      simp only [d214, d52032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7262 q = 0) : d83685 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7262, d83685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7262, d83685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d7263 q = 0) : d83686 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7263, d83686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7263, d83686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d7264 q = 0) : d83687 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d7264, d83687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7264, d83687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d7268 q = 0) : d83691 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7268, d83691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7268, d83691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4654 q selected
  have h12 (q : Pattern) (selected : d7269 q = 0) : d83692 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7269, d83692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d7269, d83692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d7270 q = 0) : d83693 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7270, d83693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d7270, d83693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d7271 q = 0) : d83694 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d7271, d83694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d7271, d83694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d7272 q = 0) : d83695 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d7272, d83695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d7272, d83695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d7287 q = 0) : d83710 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7287, d83710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7287, d83710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4657 q selected
  have h17 (q : Pattern) (selected : d7288 q = 0) : d83711 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7288, d83711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d7288, d83711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d7289 q = 0) : d83712 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7289, d83712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d7289, d83712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d7290 q = 0) : d83713 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d7290, d83713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d7290, d83713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d7291 q = 0) : d83714 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d7291, d83714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d7291, d83714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d7292 q = 0) : d83715 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d7292, d83715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d7292, d83715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro4659 (p : Pattern) (selected : d7302 p = 0) : d83725 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7248 q = 0) : d83671 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7248, d83671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4650 q selected
    | true =>
      simp only [d7248, d83671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro190 q selected
  have h2 (q : Pattern) (selected : d7298 q = 0) : d83721 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7298, d83721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7298, d83721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7299 q = 0) : d83722 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7299, d83722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7299, d83722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7300 q = 0) : d83723 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7300, d83723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7300, d83723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7301 q = 0) : d83724 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7301, d83724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7301, d83724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7302 q = 0) : d83725 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7302, d83725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7302, d83725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro4660 (p : Pattern) (selected : d7309 p = 0) : d83732 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7248 q = 0) : d83671 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7248, d83671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4650 q selected
    | true =>
      simp only [d7248, d83671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro190 q selected
  have h2 (q : Pattern) (selected : d7298 q = 0) : d83721 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7298, d83721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7298, d83721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7299 q = 0) : d83722 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7299, d83722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7299, d83722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7300 q = 0) : d83723 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7300, d83723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7300, d83723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7301 q = 0) : d83724 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7301, d83724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7301, d83724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7255 q = 0) : d83678 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7255, d83678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4652 q selected
    | true =>
      simp only [d7255, d83678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro192 q selected
  have h7 (q : Pattern) (selected : d7305 q = 0) : d83728 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7305, d83728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7305, d83728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7306 q = 0) : d83729 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7306, d83729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7306, d83729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d7307 q = 0) : d83730 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7307, d83730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7307, d83730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d7308 q = 0) : d83731 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7308, d83731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7308, d83731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d7309 q = 0) : d83732 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7309, d83732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7309, d83732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro4661 (p : Pattern) (selected : d7314 p = 0) : d83737 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7242 q = 0) : d83665 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, d83665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4649 q selected
    | true =>
      simp only [d7242, d83665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7243 q = 0) : d83666 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, d83666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7243, d83666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d37 q = 0) : d51889 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro189 q selected
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d38 q = 0) : d51890 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7244 q = 0) : d83667 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7244, d83667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7244, d83667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7245 q = 0) : d83668 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7245, d83668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7245, d83668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7313 q = 0) : d83736 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7313, d83736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7313, d83736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7314 q = 0) : d83737 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7314, d83737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7314, d83737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro4662 (p : Pattern) (selected : d7321 p = 0) : d83744 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7242 q = 0) : d83665 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, d83665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4649 q selected
    | true =>
      simp only [d7242, d83665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7243 q = 0) : d83666 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, d83666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7243, d83666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d37 q = 0) : d51889 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro189 q selected
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d38 q = 0) : d51890 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7244 q = 0) : d83667 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7244, d83667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7244, d83667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7319 q = 0) : d83742 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7319, d83742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7319, d83742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7320 q = 0) : d83743 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7320, d83743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7320, d83743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7321 q = 0) : d83744 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7321, d83744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7321, d83744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro4663 (p : Pattern) (selected : d7326 p = 0) : d83749 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d325 q = 0) : d52124 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d325, d52124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro236 q selected
    | true =>
      simp only [d325, d52124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro206 q selected
  have h2 (q : Pattern) (selected : d326 q = 0) : d52125 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d326, d52125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d326, d52125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d327 q = 0) : d52126 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d327, d52126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d327, d52126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d145 q = 0) : d51996 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d51996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro206 q selected
    | true =>
      simp only [d145, d51996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro188 q selected
  have h5 (q : Pattern) (selected : d146 q = 0) : d51997 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d51997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d146, d51997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d147 q = 0) : d51998 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d51998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d147, d51998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d328 q = 0) : d52127 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d328, d52127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d328, d52127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7325 q = 0) : d83748 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7325, d83748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7325, d83748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d7326 q = 0) : d83749 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7326, d83749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7326, d83749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro4664 (p : Pattern) (selected : d7332 p = 0) : d83755 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7327 q = 0) : d83750 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d83750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4663 q selected
    | true =>
      simp only [d7327, d83750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7328 q = 0) : d83751 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d83751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7328, d83751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7242 q = 0) : d83665 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, d83665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4649 q selected
    | true =>
      simp only [d7242, d83665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7243 q = 0) : d83666 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, d83666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7243, d83666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7329 q = 0) : d83752 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7329, d83752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7329, d83752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7330 q = 0) : d83753 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7330, d83753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7330, d83753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7331 q = 0) : d83754 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7331, d83754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7331, d83754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7332 q = 0) : d83755 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7332, d83755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7332, d83755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro4665 (p : Pattern) (selected : d7335 p = 0) : d83664 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d356 q = 0) : d51996 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d356, d51996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro241 q selected
    | true =>
      simp only [d356, d51996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro211 q selected
  have h2 (q : Pattern) (selected : d357 q = 0) : d51997 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d357, d51997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d357, d51997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d358 q = 0) : d51998 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d358, d51998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d358, d51998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d176 q = 0) : d51883 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176, d51883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro211 q selected
    | true =>
      simp only [d176, d51883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d177 q = 0) : d51884 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d177, d51884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177, d51884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d178 q = 0) : d51885 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d178, d51885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d178, d51885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d359 q = 0) : d51999 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d359, d51999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359, d51999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7334 q = 0) : d83663 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7334, d83663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7334, d83663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d7335 q = 0) : d83664 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7335, d83664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7335, d83664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro4666 (p : Pattern) (selected : d7341 p = 0) : d83670 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7336 q = 0) : d83665 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7336, d83665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4665 q selected
    | true =>
      simp only [d7336, d83665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7337 q = 0) : d83666 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7337, d83666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7337, d83666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182 q = 0) : d51889 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro212 q selected
    | true =>
      simp only [d182, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d183 q = 0) : d51890 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d183, d51890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d183, d51890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7338 q = 0) : d83667 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7338, d83667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7338, d83667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7339 q = 0) : d83668 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7339, d83668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7339, d83668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7340 q = 0) : d83669 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7340, d83669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7340, d83669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7341 q = 0) : d83670 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7341, d83670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7341, d83670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro4667 (p : Pattern) (selected : d7347 p = 0) : d83761 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7242 q = 0) : d83665 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, d83665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4649 q selected
    | true =>
      simp only [d7242, d83665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7243 q = 0) : d83666 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, d83666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7243, d83666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7344 q = 0) : d83758 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7344, d83758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7344, d83758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7345 q = 0) : d83759 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7345, d83759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7345, d83759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d7346 q = 0) : d83760 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7346, d83760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7346, d83760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d7347 q = 0) : d83761 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7347, d83761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7347, d83761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro4668 (p : Pattern) (selected : d7353 p = 0) : d83767 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7315 q = 0) : d83738 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7315, d83738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4661 q selected
    | true =>
      simp only [d7315, d83738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro202 q selected
  have h2 (q : Pattern) (selected : d7316 q = 0) : d83739 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7316, d83739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7316, d83739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7317 q = 0) : d83740 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7317, d83740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7317, d83740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7318 q = 0) : d83741 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7318, d83741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7318, d83741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7322 q = 0) : d83745 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7322, d83745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4662 q selected
    | true =>
      simp only [d7322, d83745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro203 q selected
  have h6 (q : Pattern) (selected : d7323 q = 0) : d83746 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7323, d83746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7323, d83746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7324 q = 0) : d83747 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7324, d83747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7324, d83747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7333 q = 0) : d83756 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7333, d83756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4664 q selected
    | true =>
      simp only [d7333, d83756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4650 q selected
  have h9 (q : Pattern) (selected : d7342 q = 0) : d83671 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7342, d83671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4666 q selected
    | true =>
      simp only [d7342, d83671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro213 q selected
  have h10 (q : Pattern) (selected : d7343 q = 0) : d83757 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7343, d83757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7343, d83757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d7348 q = 0) : d83762 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7348, d83762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4667 q selected
    | true =>
      simp only [d7348, d83762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d7349 q = 0) : d83763 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7349, d83763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d7349, d83763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d7350 q = 0) : d83764 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7350, d83764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d7350, d83764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d7351 q = 0) : d83765 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7351, d83765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7351, d83765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d7352 q = 0) : d83766 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7352, d83766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7352, d83766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d7353 q = 0) : d83767 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7353, d83767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7353, d83767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro4669 (p : Pattern) (selected : d7354 p = 0) : d83768 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7242 q = 0) : d83665 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, d83665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4649 q selected
    | true =>
      simp only [d7242, d83665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7243 q = 0) : d83666 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, d83666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7243, d83666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d37 q = 0) : d51889 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro189 q selected
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d38 q = 0) : d51890 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7244 q = 0) : d83667 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7244, d83667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7244, d83667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7245 q = 0) : d83668 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7245, d83668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7245, d83668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7313 q = 0) : d83736 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7313, d83736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7313, d83736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7354 q = 0) : d83768 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7354, d83768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7354, d83768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro4670 (p : Pattern) (selected : d7359 p = 0) : d83773 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7242 q = 0) : d83665 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, d83665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4649 q selected
    | true =>
      simp only [d7242, d83665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7243 q = 0) : d83666 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, d83666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7243, d83666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d37 q = 0) : d51889 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro189 q selected
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d38 q = 0) : d51890 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7244 q = 0) : d83667 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7244, d83667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7244, d83667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7319 q = 0) : d83742 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7319, d83742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7319, d83742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7320 q = 0) : d83743 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7320, d83743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7320, d83743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7359 q = 0) : d83773 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7359, d83773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7359, d83773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro4671 (p : Pattern) (selected : d7363 p = 0) : d83777 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7327 q = 0) : d83750 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d83750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4663 q selected
    | true =>
      simp only [d7327, d83750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7328 q = 0) : d83751 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d83751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7328, d83751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7242 q = 0) : d83665 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, d83665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4649 q selected
    | true =>
      simp only [d7242, d83665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7243 q = 0) : d83666 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, d83666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7243, d83666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7329 q = 0) : d83752 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7329, d83752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7329, d83752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7330 q = 0) : d83753 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7330, d83753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7330, d83753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7331 q = 0) : d83754 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7331, d83754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7331, d83754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7363 q = 0) : d83777 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7363, d83777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7363, d83777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro4672 (p : Pattern) (selected : d7365 p = 0) : d83677 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7336 q = 0) : d83665 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7336, d83665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4665 q selected
    | true =>
      simp only [d7336, d83665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7337 q = 0) : d83666 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7337, d83666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7337, d83666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182 q = 0) : d51889 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro212 q selected
    | true =>
      simp only [d182, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d183 q = 0) : d51890 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d183, d51890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d183, d51890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7338 q = 0) : d83667 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7338, d83667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7338, d83667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7339 q = 0) : d83668 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7339, d83668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7339, d83668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7340 q = 0) : d83669 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7340, d83669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7340, d83669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7365 q = 0) : d83677 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7365, d83677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7365, d83677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro4673 (p : Pattern) (selected : d7368 p = 0) : d83780 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7242 q = 0) : d83665 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, d83665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4649 q selected
    | true =>
      simp only [d7242, d83665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7243 q = 0) : d83666 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, d83666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7243, d83666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7344 q = 0) : d83758 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7344, d83758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7344, d83758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7345 q = 0) : d83759 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7345, d83759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7345, d83759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d7346 q = 0) : d83760 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7346, d83760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7346, d83760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d7368 q = 0) : d83780 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7368, d83780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7368, d83780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4674 (p : Pattern) (selected : d7374 p = 0) : d83786 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7315 q = 0) : d83738 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7315, d83738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4661 q selected
    | true =>
      simp only [d7315, d83738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro202 q selected
  have h2 (q : Pattern) (selected : d7316 q = 0) : d83739 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7316, d83739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7316, d83739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7317 q = 0) : d83740 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7317, d83740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7317, d83740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7318 q = 0) : d83741 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7318, d83741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7318, d83741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7322 q = 0) : d83745 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7322, d83745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4662 q selected
    | true =>
      simp only [d7322, d83745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro203 q selected
  have h6 (q : Pattern) (selected : d7323 q = 0) : d83746 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7323, d83746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7323, d83746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7324 q = 0) : d83747 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7324, d83747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7324, d83747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7333 q = 0) : d83756 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7333, d83756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4664 q selected
    | true =>
      simp only [d7333, d83756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4650 q selected
  have h9 (q : Pattern) (selected : d7342 q = 0) : d83671 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7342, d83671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4666 q selected
    | true =>
      simp only [d7342, d83671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro213 q selected
  have h10 (q : Pattern) (selected : d7343 q = 0) : d83757 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7343, d83757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7343, d83757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d7348 q = 0) : d83762 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7348, d83762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4667 q selected
    | true =>
      simp only [d7348, d83762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d7349 q = 0) : d83763 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7349, d83763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d7349, d83763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d7350 q = 0) : d83764 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7350, d83764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d7350, d83764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d7351 q = 0) : d83765 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7351, d83765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7351, d83765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d7352 q = 0) : d83766 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7352, d83766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7352, d83766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d7355 q = 0) : d83769 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7355, d83769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4669 q selected
    | true =>
      simp only [d7355, d83769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro215 q selected
  have h17 (q : Pattern) (selected : d7356 q = 0) : d83770 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7356, d83770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7356, d83770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d7357 q = 0) : d83771 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7357, d83771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d7357, d83771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d7358 q = 0) : d83772 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7358, d83772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7358, d83772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d7360 q = 0) : d83774 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7360, d83774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4670 q selected
    | true =>
      simp only [d7360, d83774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro216 q selected
  have h21 (q : Pattern) (selected : d7361 q = 0) : d83775 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7361, d83775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7361, d83775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d7362 q = 0) : d83776 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7362, d83776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d7362, d83776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d7364 q = 0) : d83778 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7364, d83778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4671 q selected
    | true =>
      simp only [d7364, d83778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4652 q selected
  have h24 (q : Pattern) (selected : d7366 q = 0) : d83678 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7366, d83678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4672 q selected
    | true =>
      simp only [d7366, d83678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro218 q selected
  have h25 (q : Pattern) (selected : d7367 q = 0) : d83779 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7367, d83779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d7367, d83779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d7369 q = 0) : d83781 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7369, d83781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4673 q selected
    | true =>
      simp only [d7369, d83781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d7370 q = 0) : d83782 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7370, d83782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d7370, d83782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d7371 q = 0) : d83783 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7371, d83783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d7371, d83783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d7372 q = 0) : d83784 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7372, d83784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d7372, d83784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d7373 q = 0) : d83785 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7373, d83785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d7373, d83785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d7374 q = 0) : d83786 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7374, d83786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d7374, d83786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro4675 (p : Pattern) (selected : d7376 p = 0) : d83788 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7248 q = 0) : d83671 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7248, d83671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4650 q selected
    | true =>
      simp only [d7248, d83671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro190 q selected
  have h2 (q : Pattern) (selected : d7298 q = 0) : d83721 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7298, d83721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7298, d83721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7299 q = 0) : d83722 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7299, d83722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7299, d83722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7300 q = 0) : d83723 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7300, d83723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7300, d83723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7301 q = 0) : d83724 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7301, d83724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7301, d83724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d43 q = 0) : d51895 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro190 q selected
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d100 q = 0) : d51952 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d51952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d100, d51952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d101 q = 0) : d51953 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d51953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d101, d51953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d102 q = 0) : d51954 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, d51954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d102, d51954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d103 q = 0) : d51955 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, d51955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103, d51955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d7376 q = 0) : d83788 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7376, d83788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7376, d83788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro4676 (p : Pattern) (selected : d7383 p = 0) : d83795 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7364 q = 0) : d83778 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7364, d83778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4671 q selected
    | true =>
      simp only [d7364, d83778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4652 q selected
  have h2 (q : Pattern) (selected : d7366 q = 0) : d83678 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7366, d83678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4672 q selected
    | true =>
      simp only [d7366, d83678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro218 q selected
  have h3 (q : Pattern) (selected : d7367 q = 0) : d83779 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7367, d83779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d7367, d83779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d7369 q = 0) : d83781 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7369, d83781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4673 q selected
    | true =>
      simp only [d7369, d83781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d7370 q = 0) : d83782 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7370, d83782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7370, d83782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d7371 q = 0) : d83783 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7371, d83783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7371, d83783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7381 q = 0) : d83793 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7381, d83793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7381, d83793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7382 q = 0) : d83794 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7382, d83794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7382, d83794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d7383 q = 0) : d83795 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7383, d83795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7383, d83795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro4677 (p : Pattern) (selected : d7390 p = 0) : d83802 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d418 q = 0) : d52184 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d418, d52184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro253 q selected
    | true =>
      simp only [d418, d52184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro222 q selected
  have h2 (q : Pattern) (selected : d419 q = 0) : d52185 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d419, d52185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d419, d52185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d420 q = 0) : d52186 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d420, d52186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d420, d52186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232 q = 0) : d52050 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d52050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro222 q selected
    | true =>
      simp only [d232, d52050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro195 q selected
  have h5 (q : Pattern) (selected : d233 q = 0) : d52051 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d52051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233, d52051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d234 q = 0) : d52052 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d52052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d234, d52052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d421 q = 0) : d52187 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d421, d52187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d421, d52187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7389 q = 0) : d83801 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7389, d83801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7389, d83801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d7390 q = 0) : d83802 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7390, d83802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7390, d83802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro4678 (p : Pattern) (selected : d7396 p = 0) : d83808 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7391 q = 0) : d83803 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7391, d83803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4677 q selected
    | true =>
      simp only [d7391, d83803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7392 q = 0) : d83804 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7392, d83804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7392, d83804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7275 q = 0) : d83698 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7275, d83698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4655 q selected
    | true =>
      simp only [d7275, d83698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7276 q = 0) : d83699 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7276, d83699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7276, d83699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7393 q = 0) : d83805 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7393, d83805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7393, d83805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7394 q = 0) : d83806 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7394, d83806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7394, d83806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7395 q = 0) : d83807 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7395, d83807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7395, d83807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7396 q = 0) : d83808 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7396, d83808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7396, d83808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro4679 (p : Pattern) (selected : d7399 p = 0) : d83697 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d437 q = 0) : d52050 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d437, d52050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro256 q selected
    | true =>
      simp only [d437, d52050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro225 q selected
  have h2 (q : Pattern) (selected : d438 q = 0) : d52051 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d438, d52051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d438, d52051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d439 q = 0) : d52052 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d439, d52052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d439, d52052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d251 q = 0) : d51924 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d251, d51924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro225 q selected
    | true =>
      simp only [d251, d51924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d252 q = 0) : d51925 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d252, d51925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d252, d51925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d253 q = 0) : d51926 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d253, d51926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d253, d51926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d440 q = 0) : d52053 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d440, d52053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d440, d52053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7398 q = 0) : d83696 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7398, d83696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7398, d83696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d7399 q = 0) : d83697 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7399, d83697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7399, d83697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro4680 (p : Pattern) (selected : d7405 p = 0) : d83703 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7400 q = 0) : d83698 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7400, d83698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4679 q selected
    | true =>
      simp only [d7400, d83698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7401 q = 0) : d83699 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7401, d83699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7401, d83699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d257 q = 0) : d51930 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d257, d51930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro226 q selected
    | true =>
      simp only [d257, d51930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d258 q = 0) : d51931 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d258, d51931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d258, d51931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7402 q = 0) : d83700 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7402, d83700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7402, d83700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7403 q = 0) : d83701 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7403, d83701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7403, d83701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7404 q = 0) : d83702 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7404, d83702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7404, d83702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7405 q = 0) : d83703 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7405, d83703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7405, d83703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro4681 (p : Pattern) (selected : d7411 p = 0) : d83814 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7275 q = 0) : d83698 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7275, d83698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4655 q selected
    | true =>
      simp only [d7275, d83698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7276 q = 0) : d83699 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7276, d83699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7276, d83699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7408 q = 0) : d83811 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7408, d83811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7408, d83811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7409 q = 0) : d83812 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7409, d83812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7409, d83812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d7410 q = 0) : d83813 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7410, d83813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7410, d83813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d7411 q = 0) : d83814 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7411, d83814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7411, d83814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4682 (p : Pattern) (selected : d7417 p = 0) : d83820 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7397 q = 0) : d83809 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7397, d83809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4678 q selected
    | true =>
      simp only [d7397, d83809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4656 q selected
  have h2 (q : Pattern) (selected : d7406 q = 0) : d83704 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7406, d83704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4680 q selected
    | true =>
      simp only [d7406, d83704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro227 q selected
  have h3 (q : Pattern) (selected : d7407 q = 0) : d83810 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7407, d83810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d7407, d83810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d7412 q = 0) : d83815 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7412, d83815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4681 q selected
    | true =>
      simp only [d7412, d83815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d7413 q = 0) : d83816 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7413, d83816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7413, d83816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d7414 q = 0) : d83817 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7414, d83817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7414, d83817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7415 q = 0) : d83818 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7415, d83818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7415, d83818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7416 q = 0) : d83819 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7416, d83819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7416, d83819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d7417 q = 0) : d83820 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7417, d83820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7417, d83820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro4683 (p : Pattern) (selected : d7423 p = 0) : d83826 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7303 q = 0) : d83726 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7303, d83726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7303, d83726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4659 q selected
  have h2 (q : Pattern) (selected : d7304 q = 0) : d83727 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7304, d83727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d7304, d83727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d7310 q = 0) : d83733 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7310, d83733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4659 q selected
    | true =>
      simp only [d7310, d83733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4660 q selected
  have h4 (q : Pattern) (selected : d7311 q = 0) : d83734 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7311, d83734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7311, d83734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d7312 q = 0) : d83735 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7312, d83735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7312, d83735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7375 q = 0) : d83787 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7375, d83787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4668 q selected
    | true =>
      simp only [d7375, d83787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4674 q selected
  have h7 (q : Pattern) (selected : d7377 q = 0) : d83789 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7377, d83789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4675 q selected
    | true =>
      simp only [d7377, d83789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro201 q selected
  have h8 (q : Pattern) (selected : d7378 q = 0) : d83790 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7378, d83790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7378, d83790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d7379 q = 0) : d83791 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7379, d83791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7379, d83791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d7380 q = 0) : d83792 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d7380, d83792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7380, d83792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d7384 q = 0) : d83796 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7384, d83796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7384, d83796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4676 q selected
  have h12 (q : Pattern) (selected : d407 q = 0) : d52173 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, d52173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d407, d52173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro252 q selected
  have h13 (q : Pattern) (selected : d7385 q = 0) : d83797 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7385, d83797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d7385, d83797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d7386 q = 0) : d83798 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7386, d83798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d7386, d83798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d7387 q = 0) : d83799 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d7387, d83799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d7387, d83799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d7388 q = 0) : d83800 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d7388, d83800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d7388, d83800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d7418 q = 0) : d83821 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7418, d83821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7418, d83821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4682 q selected
  have h18 (q : Pattern) (selected : d463 q = 0) : d52210 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, d52210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d463, d52210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro260 q selected
  have h19 (q : Pattern) (selected : d7419 q = 0) : d83822 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7419, d83822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d7419, d83822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d7420 q = 0) : d83823 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7420, d83823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d7420, d83823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d7421 q = 0) : d83824 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d7421, d83824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d7421, d83824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d7422 q = 0) : d83825 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d7422, d83825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d7422, d83825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d7423 q = 0) : d83826 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d7423, d83826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d7423, d83826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro4684 (p : Pattern) (selected : d7429 p = 0) : d83832 p = 1 := by
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
  have h5 (q : Pattern) (selected : d7293 q = 0) : d83716 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d7293, d83716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7293, d83716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4658 q selected
  have h6 (q : Pattern) (selected : d7294 q = 0) : d83717 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d7294, d83717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7294, d83717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7295 q = 0) : d83718 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d7295, d83718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7295, d83718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7296 q = 0) : d83719 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d7296, d83719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7296, d83719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d7297 q = 0) : d83720 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d7297, d83720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7297, d83720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d7424 q = 0) : d83827 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d7424, d83827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7424, d83827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4683 q selected
  have h11 (q : Pattern) (selected : d7425 q = 0) : d83828 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d7425, d83828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7425, d83828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d7426 q = 0) : d83829 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d7426, d83829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7426, d83829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d7427 q = 0) : d83830 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d7427, d83830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7427, d83830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d7428 q = 0) : d83831 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d7428, d83831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7428, d83831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d7429 q = 0) : d83832 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d7429, d83832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d7429, d83832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro4685 (p : Pattern) (selected : d7433 p = 0) : d83836 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7327 q = 0) : d83750 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d83750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4663 q selected
    | true =>
      simp only [d7327, d83750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7328 q = 0) : d83751 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d83751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7328, d83751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d482 q = 0) : d52229 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro264 q selected
    | true =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d483 q = 0) : d52230 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7430 q = 0) : d83833 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7430, d83833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7430, d83833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7431 q = 0) : d83834 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7431, d83834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7431, d83834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7432 q = 0) : d83835 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7432, d83835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7432, d83835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7433 q = 0) : d83836 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7433, d83836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7433, d83836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro4686 (p : Pattern) (selected : d7439 p = 0) : d83842 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7434 q = 0) : d83837 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7434, d83837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4685 q selected
    | true =>
      simp only [d7434, d83837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro266 q selected
  have h2 (q : Pattern) (selected : d7435 q = 0) : d83838 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7435, d83838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7435, d83838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7436 q = 0) : d83839 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7436, d83839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7436, d83839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7437 q = 0) : d83840 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7437, d83840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7437, d83840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7438 q = 0) : d83841 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7438, d83841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7438, d83841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7439 q = 0) : d83842 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7439, d83842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7439, d83842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro4687 (p : Pattern) (selected : d7442 p = 0) : d83845 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7327 q = 0) : d83750 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d83750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4663 q selected
    | true =>
      simp only [d7327, d83750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7328 q = 0) : d83751 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d83751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7328, d83751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d482 q = 0) : d52229 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro264 q selected
    | true =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d483 q = 0) : d52230 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7430 q = 0) : d83833 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7430, d83833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7430, d83833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7431 q = 0) : d83834 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7431, d83834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7431, d83834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7432 q = 0) : d83835 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7432, d83835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7432, d83835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7442 q = 0) : d83845 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7442, d83845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7442, d83845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro4688 (p : Pattern) (selected : d7448 p = 0) : d83851 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7434 q = 0) : d83837 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7434, d83837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4685 q selected
    | true =>
      simp only [d7434, d83837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro266 q selected
  have h2 (q : Pattern) (selected : d7435 q = 0) : d83838 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7435, d83838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7435, d83838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7436 q = 0) : d83839 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7436, d83839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7436, d83839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7437 q = 0) : d83840 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7437, d83840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7437, d83840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7438 q = 0) : d83841 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7438, d83841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7438, d83841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7443 q = 0) : d83846 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7443, d83846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4687 q selected
    | true =>
      simp only [d7443, d83846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro269 q selected
  have h7 (q : Pattern) (selected : d7444 q = 0) : d83847 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7444, d83847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7444, d83847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7445 q = 0) : d83848 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7445, d83848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7445, d83848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d7446 q = 0) : d83849 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7446, d83849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7446, d83849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d7447 q = 0) : d83850 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7447, d83850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7447, d83850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d7448 q = 0) : d83851 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7448, d83851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7448, d83851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro4689 (p : Pattern) (selected : d7453 p = 0) : d83856 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7327 q = 0) : d83750 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d83750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4663 q selected
    | true =>
      simp only [d7327, d83750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7328 q = 0) : d83751 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d83751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7328, d83751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d482 q = 0) : d52229 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro264 q selected
    | true =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d483 q = 0) : d52230 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7430 q = 0) : d83833 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7430, d83833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7430, d83833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7431 q = 0) : d83834 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7431, d83834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7431, d83834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7452 q = 0) : d83855 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7452, d83855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7452, d83855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7453 q = 0) : d83856 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7453, d83856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7453, d83856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro4690 (p : Pattern) (selected : d7460 p = 0) : d83863 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7327 q = 0) : d83750 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d83750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4663 q selected
    | true =>
      simp only [d7327, d83750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7328 q = 0) : d83751 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d83751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7328, d83751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d482 q = 0) : d52229 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro264 q selected
    | true =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d483 q = 0) : d52230 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7430 q = 0) : d83833 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7430, d83833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7430, d83833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7458 q = 0) : d83861 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7458, d83861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7458, d83861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7459 q = 0) : d83862 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7459, d83862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7459, d83862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7460 q = 0) : d83863 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7460, d83863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7460, d83863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro4691 (p : Pattern) (selected : d7465 p = 0) : d83868 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d549 q = 0) : d52296 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d549, d52296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro278 q selected
    | true =>
      simp only [d549, d52296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro236 q selected
  have h2 (q : Pattern) (selected : d550 q = 0) : d52297 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d550, d52297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d550, d52297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d551 q = 0) : d52298 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d551, d52298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d551, d52298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d325 q = 0) : d52124 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d325, d52124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro236 q selected
    | true =>
      simp only [d325, d52124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro206 q selected
  have h5 (q : Pattern) (selected : d326 q = 0) : d52125 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d326, d52125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d326, d52125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d327 q = 0) : d52126 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d327, d52126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d327, d52126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d552 q = 0) : d52299 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d552, d52299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d552, d52299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7464 q = 0) : d83867 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7464, d83867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7464, d83867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d7465 q = 0) : d83868 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7465, d83868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7465, d83868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro4692 (p : Pattern) (selected : d7471 p = 0) : d83874 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7466 q = 0) : d83869 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7466, d83869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4691 q selected
    | true =>
      simp only [d7466, d83869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7467 q = 0) : d83870 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7467, d83870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7467, d83870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7327 q = 0) : d83750 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d83750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4663 q selected
    | true =>
      simp only [d7327, d83750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7328 q = 0) : d83751 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d83751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7328, d83751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7468 q = 0) : d83871 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7468, d83871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7468, d83871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7469 q = 0) : d83872 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7469, d83872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7469, d83872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7470 q = 0) : d83873 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7470, d83873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7470, d83873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7471 q = 0) : d83874 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7471, d83874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7471, d83874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro4693 (p : Pattern) (selected : d7474 p = 0) : d83749 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d580 q = 0) : d52124 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d580, d52124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro283 q selected
    | true =>
      simp only [d580, d52124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro241 q selected
  have h2 (q : Pattern) (selected : d581 q = 0) : d52125 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d581, d52125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d581, d52125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d582 q = 0) : d52126 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d582, d52126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d582, d52126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d356 q = 0) : d51996 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d356, d51996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro241 q selected
    | true =>
      simp only [d356, d51996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro211 q selected
  have h5 (q : Pattern) (selected : d357 q = 0) : d51997 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d357, d51997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d357, d51997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d358 q = 0) : d51998 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d358, d51998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d358, d51998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d583 q = 0) : d52127 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d583, d52127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d583, d52127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7473 q = 0) : d83748 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7473, d83748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7473, d83748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d7474 q = 0) : d83749 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7474, d83749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7474, d83749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro4694 (p : Pattern) (selected : d7480 p = 0) : d83836 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7475 q = 0) : d83750 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7475, d83750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4693 q selected
    | true =>
      simp only [d7475, d83750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7476 q = 0) : d83751 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7476, d83751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7476, d83751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d591 q = 0) : d52229 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d591, d52229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro285 q selected
    | true =>
      simp only [d591, d52229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d592 q = 0) : d52230 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d592, d52230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d592, d52230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7477 q = 0) : d83833 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7477, d83833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7477, d83833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7478 q = 0) : d83834 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7478, d83834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7478, d83834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7479 q = 0) : d83835 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7479, d83835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7479, d83835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7480 q = 0) : d83836 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7480, d83836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7480, d83836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro4695 (p : Pattern) (selected : d7486 p = 0) : d83880 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7327 q = 0) : d83750 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d83750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4663 q selected
    | true =>
      simp only [d7327, d83750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7328 q = 0) : d83751 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d83751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7328, d83751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7483 q = 0) : d83877 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7483, d83877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7483, d83877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7484 q = 0) : d83878 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7484, d83878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7484, d83878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d7485 q = 0) : d83879 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7485, d83879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7485, d83879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d7486 q = 0) : d83880 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7486, d83880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7486, d83880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro4696 (p : Pattern) (selected : d7492 p = 0) : d83886 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7454 q = 0) : d83857 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7454, d83857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4689 q selected
    | true =>
      simp only [d7454, d83857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro272 q selected
  have h2 (q : Pattern) (selected : d7455 q = 0) : d83858 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7455, d83858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7455, d83858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7456 q = 0) : d83859 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7456, d83859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7456, d83859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7457 q = 0) : d83860 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7457, d83860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7457, d83860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7461 q = 0) : d83864 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7461, d83864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4690 q selected
    | true =>
      simp only [d7461, d83864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro274 q selected
  have h6 (q : Pattern) (selected : d7462 q = 0) : d83865 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7462, d83865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7462, d83865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7463 q = 0) : d83866 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7463, d83866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7463, d83866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7472 q = 0) : d83875 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7472, d83875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4692 q selected
    | true =>
      simp only [d7472, d83875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4685 q selected
  have h9 (q : Pattern) (selected : d7481 q = 0) : d83837 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7481, d83837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4694 q selected
    | true =>
      simp only [d7481, d83837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro287 q selected
  have h10 (q : Pattern) (selected : d7482 q = 0) : d83876 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7482, d83876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7482, d83876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d7487 q = 0) : d83881 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7487, d83881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4695 q selected
    | true =>
      simp only [d7487, d83881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d7488 q = 0) : d83882 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7488, d83882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d7488, d83882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d7489 q = 0) : d83883 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7489, d83883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d7489, d83883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d7490 q = 0) : d83884 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7490, d83884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7490, d83884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d7491 q = 0) : d83885 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7491, d83885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7491, d83885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d7492 q = 0) : d83886 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7492, d83886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7492, d83886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro4697 (p : Pattern) (selected : d7493 p = 0) : d83887 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7327 q = 0) : d83750 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d83750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4663 q selected
    | true =>
      simp only [d7327, d83750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7328 q = 0) : d83751 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d83751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7328, d83751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d482 q = 0) : d52229 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro264 q selected
    | true =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d483 q = 0) : d52230 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7430 q = 0) : d83833 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7430, d83833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7430, d83833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7431 q = 0) : d83834 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7431, d83834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7431, d83834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7452 q = 0) : d83855 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7452, d83855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7452, d83855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7493 q = 0) : d83887 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7493, d83887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7493, d83887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro4698 (p : Pattern) (selected : d7498 p = 0) : d83892 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7327 q = 0) : d83750 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d83750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4663 q selected
    | true =>
      simp only [d7327, d83750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7328 q = 0) : d83751 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d83751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7328, d83751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d482 q = 0) : d52229 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro264 q selected
    | true =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d483 q = 0) : d52230 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7430 q = 0) : d83833 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7430, d83833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7430, d83833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7458 q = 0) : d83861 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7458, d83861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7458, d83861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7459 q = 0) : d83862 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7459, d83862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7459, d83862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7498 q = 0) : d83892 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7498, d83892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7498, d83892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro4699 (p : Pattern) (selected : d7502 p = 0) : d83896 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7466 q = 0) : d83869 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7466, d83869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4691 q selected
    | true =>
      simp only [d7466, d83869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7467 q = 0) : d83870 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7467, d83870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7467, d83870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7327 q = 0) : d83750 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d83750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4663 q selected
    | true =>
      simp only [d7327, d83750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7328 q = 0) : d83751 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d83751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7328, d83751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7468 q = 0) : d83871 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7468, d83871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7468, d83871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7469 q = 0) : d83872 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7469, d83872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7469, d83872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7470 q = 0) : d83873 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7470, d83873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7470, d83873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7502 q = 0) : d83896 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7502, d83896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7502, d83896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro4700 (p : Pattern) (selected : d7504 p = 0) : d83845 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7475 q = 0) : d83750 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7475, d83750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4693 q selected
    | true =>
      simp only [d7475, d83750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7476 q = 0) : d83751 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7476, d83751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7476, d83751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d591 q = 0) : d52229 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d591, d52229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro285 q selected
    | true =>
      simp only [d591, d52229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d592 q = 0) : d52230 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d592, d52230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d592, d52230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7477 q = 0) : d83833 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7477, d83833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7477, d83833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7478 q = 0) : d83834 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7478, d83834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7478, d83834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7479 q = 0) : d83835 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7479, d83835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7479, d83835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7504 q = 0) : d83845 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7504, d83845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7504, d83845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro4701 (p : Pattern) (selected : d7507 p = 0) : d83899 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7327 q = 0) : d83750 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d83750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4663 q selected
    | true =>
      simp only [d7327, d83750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7328 q = 0) : d83751 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d83751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7328, d83751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7483 q = 0) : d83877 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7483, d83877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7483, d83877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7484 q = 0) : d83878 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7484, d83878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7484, d83878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d7485 q = 0) : d83879 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7485, d83879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7485, d83879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d7507 q = 0) : d83899 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7507, d83899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7507, d83899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4702 (p : Pattern) (selected : d7513 p = 0) : d83905 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7454 q = 0) : d83857 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7454, d83857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4689 q selected
    | true =>
      simp only [d7454, d83857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro272 q selected
  have h2 (q : Pattern) (selected : d7455 q = 0) : d83858 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7455, d83858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7455, d83858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7456 q = 0) : d83859 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7456, d83859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7456, d83859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7457 q = 0) : d83860 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7457, d83860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7457, d83860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7461 q = 0) : d83864 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7461, d83864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4690 q selected
    | true =>
      simp only [d7461, d83864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro274 q selected
  have h6 (q : Pattern) (selected : d7462 q = 0) : d83865 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7462, d83865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7462, d83865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7463 q = 0) : d83866 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7463, d83866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7463, d83866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7472 q = 0) : d83875 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7472, d83875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4692 q selected
    | true =>
      simp only [d7472, d83875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4685 q selected
  have h9 (q : Pattern) (selected : d7481 q = 0) : d83837 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7481, d83837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4694 q selected
    | true =>
      simp only [d7481, d83837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro287 q selected
  have h10 (q : Pattern) (selected : d7482 q = 0) : d83876 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7482, d83876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7482, d83876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d7487 q = 0) : d83881 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7487, d83881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4695 q selected
    | true =>
      simp only [d7487, d83881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d7488 q = 0) : d83882 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7488, d83882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d7488, d83882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d7489 q = 0) : d83883 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7489, d83883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d7489, d83883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d7490 q = 0) : d83884 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7490, d83884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7490, d83884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d7491 q = 0) : d83885 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7491, d83885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7491, d83885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d7494 q = 0) : d83888 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7494, d83888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4697 q selected
    | true =>
      simp only [d7494, d83888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro290 q selected
  have h17 (q : Pattern) (selected : d7495 q = 0) : d83889 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7495, d83889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7495, d83889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d7496 q = 0) : d83890 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7496, d83890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d7496, d83890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d7497 q = 0) : d83891 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7497, d83891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7497, d83891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d7499 q = 0) : d83893 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7499, d83893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4698 q selected
    | true =>
      simp only [d7499, d83893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro292 q selected
  have h21 (q : Pattern) (selected : d7500 q = 0) : d83894 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7500, d83894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7500, d83894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d7501 q = 0) : d83895 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7501, d83895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d7501, d83895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d7503 q = 0) : d83897 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7503, d83897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4699 q selected
    | true =>
      simp only [d7503, d83897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4687 q selected
  have h24 (q : Pattern) (selected : d7505 q = 0) : d83846 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7505, d83846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4700 q selected
    | true =>
      simp only [d7505, d83846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro295 q selected
  have h25 (q : Pattern) (selected : d7506 q = 0) : d83898 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7506, d83898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d7506, d83898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d7508 q = 0) : d83900 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7508, d83900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4701 q selected
    | true =>
      simp only [d7508, d83900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d7509 q = 0) : d83901 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7509, d83901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d7509, d83901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d7510 q = 0) : d83902 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7510, d83902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d7510, d83902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d7511 q = 0) : d83903 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7511, d83903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d7511, d83903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d7512 q = 0) : d83904 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7512, d83904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d7512, d83904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d7513 q = 0) : d83905 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7513, d83905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d7513, d83905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro4703 (p : Pattern) (selected : d7515 p = 0) : d83907 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7434 q = 0) : d83837 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7434, d83837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4685 q selected
    | true =>
      simp only [d7434, d83837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro266 q selected
  have h2 (q : Pattern) (selected : d7435 q = 0) : d83838 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7435, d83838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7435, d83838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7436 q = 0) : d83839 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7436, d83839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7436, d83839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7437 q = 0) : d83840 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7437, d83840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7437, d83840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7438 q = 0) : d83841 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7438, d83841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7438, d83841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d633 q = 0) : d52337 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d633, d52337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro266 q selected
    | true =>
      simp only [d633, d52337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d634 q = 0) : d52338 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d634, d52338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d634, d52338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d635 q = 0) : d52339 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d635, d52339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d635, d52339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d636 q = 0) : d52340 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d636, d52340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d636, d52340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d637 q = 0) : d52341 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d637, d52341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d637, d52341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d7515 q = 0) : d83907 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7515, d83907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7515, d83907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro4704 (p : Pattern) (selected : d7522 p = 0) : d83914 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7503 q = 0) : d83897 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7503, d83897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4699 q selected
    | true =>
      simp only [d7503, d83897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4687 q selected
  have h2 (q : Pattern) (selected : d7505 q = 0) : d83846 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7505, d83846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4700 q selected
    | true =>
      simp only [d7505, d83846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro295 q selected
  have h3 (q : Pattern) (selected : d7506 q = 0) : d83898 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7506, d83898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d7506, d83898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d7508 q = 0) : d83900 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7508, d83900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4701 q selected
    | true =>
      simp only [d7508, d83900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d7509 q = 0) : d83901 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7509, d83901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7509, d83901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d7510 q = 0) : d83902 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7510, d83902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7510, d83902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7520 q = 0) : d83912 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7520, d83912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7520, d83912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7521 q = 0) : d83913 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7521, d83913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7521, d83913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d7522 q = 0) : d83914 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7522, d83914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7522, d83914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro4705 (p : Pattern) (selected : d7529 p = 0) : d83921 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d665 q = 0) : d52369 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d665, d52369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro301 q selected
    | true =>
      simp only [d665, d52369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro253 q selected
  have h2 (q : Pattern) (selected : d666 q = 0) : d52370 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d666, d52370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d666, d52370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d667 q = 0) : d52371 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d667, d52371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d667, d52371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d418 q = 0) : d52184 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d418, d52184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro253 q selected
    | true =>
      simp only [d418, d52184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro222 q selected
  have h5 (q : Pattern) (selected : d419 q = 0) : d52185 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d419, d52185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d419, d52185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d420 q = 0) : d52186 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d420, d52186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d420, d52186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d668 q = 0) : d52372 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d668, d52372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d668, d52372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7528 q = 0) : d83920 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7528, d83920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7528, d83920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d7529 q = 0) : d83921 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7529, d83921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7529, d83921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro4706 (p : Pattern) (selected : d7535 p = 0) : d83927 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7530 q = 0) : d83922 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7530, d83922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4705 q selected
    | true =>
      simp only [d7530, d83922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7531 q = 0) : d83923 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7531, d83923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7531, d83923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7391 q = 0) : d83803 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7391, d83803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4677 q selected
    | true =>
      simp only [d7391, d83803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7392 q = 0) : d83804 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7392, d83804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7392, d83804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7532 q = 0) : d83924 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7532, d83924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7532, d83924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7533 q = 0) : d83925 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7533, d83925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7533, d83925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7534 q = 0) : d83926 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7534, d83926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7534, d83926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7535 q = 0) : d83927 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7535, d83927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7535, d83927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro4707 (p : Pattern) (selected : d7539 p = 0) : d83931 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7391 q = 0) : d83803 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7391, d83803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4677 q selected
    | true =>
      simp only [d7391, d83803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7392 q = 0) : d83804 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7392, d83804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7392, d83804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d684 q = 0) : d52388 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d684, d52388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro305 q selected
    | true =>
      simp only [d684, d52388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d685 q = 0) : d52389 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d685, d52389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d685, d52389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7536 q = 0) : d83928 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7536, d83928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7536, d83928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7537 q = 0) : d83929 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7537, d83929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7537, d83929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7538 q = 0) : d83930 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7538, d83930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7538, d83930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7539 q = 0) : d83931 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7539, d83931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7539, d83931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro4708 (p : Pattern) (selected : d7542 p = 0) : d83802 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d697 q = 0) : d52184 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d697, d52184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro307 q selected
    | true =>
      simp only [d697, d52184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro256 q selected
  have h2 (q : Pattern) (selected : d698 q = 0) : d52185 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d698, d52185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d698, d52185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d699 q = 0) : d52186 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d699, d52186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d699, d52186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d437 q = 0) : d52050 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d437, d52050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro256 q selected
    | true =>
      simp only [d437, d52050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro225 q selected
  have h5 (q : Pattern) (selected : d438 q = 0) : d52051 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d438, d52051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d438, d52051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d439 q = 0) : d52052 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d439, d52052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d439, d52052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d700 q = 0) : d52187 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d700, d52187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d700, d52187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7541 q = 0) : d83801 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7541, d83801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7541, d83801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d7542 q = 0) : d83802 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7542, d83802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7542, d83802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro4709 (p : Pattern) (selected : d7548 p = 0) : d83931 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7543 q = 0) : d83803 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7543, d83803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4708 q selected
    | true =>
      simp only [d7543, d83803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7544 q = 0) : d83804 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7544, d83804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7544, d83804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d708 q = 0) : d52388 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d708, d52388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro309 q selected
    | true =>
      simp only [d708, d52388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d709 q = 0) : d52389 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d709, d52389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d709, d52389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7545 q = 0) : d83928 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7545, d83928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7545, d83928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7546 q = 0) : d83929 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7546, d83929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7546, d83929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7547 q = 0) : d83930 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7547, d83930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7547, d83930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7548 q = 0) : d83931 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7548, d83931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7548, d83931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro4710 (p : Pattern) (selected : d7554 p = 0) : d83938 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7391 q = 0) : d83803 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7391, d83803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4677 q selected
    | true =>
      simp only [d7391, d83803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7392 q = 0) : d83804 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7392, d83804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7392, d83804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7551 q = 0) : d83935 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7551, d83935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7551, d83935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7552 q = 0) : d83936 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7552, d83936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7552, d83936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d7553 q = 0) : d83937 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7553, d83937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7553, d83937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d7554 q = 0) : d83938 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7554, d83938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7554, d83938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4711 (p : Pattern) (selected : d7560 p = 0) : d83944 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7540 q = 0) : d83932 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7540, d83932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4706 q selected
    | true =>
      simp only [d7540, d83932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4707 q selected
  have h2 (q : Pattern) (selected : d7549 q = 0) : d83933 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7549, d83933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4709 q selected
    | true =>
      simp only [d7549, d83933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro311 q selected
  have h3 (q : Pattern) (selected : d7550 q = 0) : d83934 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7550, d83934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d7550, d83934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d7555 q = 0) : d83939 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7555, d83939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4710 q selected
    | true =>
      simp only [d7555, d83939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d7556 q = 0) : d83940 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7556, d83940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7556, d83940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d7557 q = 0) : d83941 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7557, d83941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7557, d83941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7558 q = 0) : d83942 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7558, d83942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7558, d83942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7559 q = 0) : d83943 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7559, d83943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7559, d83943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d7560 q = 0) : d83944 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7560, d83944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7560, d83944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro4712 (p : Pattern) (selected : d7566 p = 0) : d83950 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7440 q = 0) : d83843 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7440, d83843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7440, d83843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4686 q selected
  have h2 (q : Pattern) (selected : d7441 q = 0) : d83844 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7441, d83844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d7441, d83844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d7449 q = 0) : d83852 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7449, d83852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4686 q selected
    | true =>
      simp only [d7449, d83852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4688 q selected
  have h4 (q : Pattern) (selected : d7450 q = 0) : d83853 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7450, d83853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7450, d83853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d7451 q = 0) : d83854 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7451, d83854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7451, d83854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7514 q = 0) : d83906 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7514, d83906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4696 q selected
    | true =>
      simp only [d7514, d83906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4702 q selected
  have h7 (q : Pattern) (selected : d7516 q = 0) : d83908 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7516, d83908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4703 q selected
    | true =>
      simp only [d7516, d83908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro298 q selected
  have h8 (q : Pattern) (selected : d7517 q = 0) : d83909 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7517, d83909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7517, d83909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d7518 q = 0) : d83910 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7518, d83910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7518, d83910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d7519 q = 0) : d83911 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d7519, d83911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7519, d83911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d7523 q = 0) : d83915 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7523, d83915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7523, d83915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4704 q selected
  have h12 (q : Pattern) (selected : d654 q = 0) : d52358 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d654, d52358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d654, d52358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro300 q selected
  have h13 (q : Pattern) (selected : d7524 q = 0) : d83916 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7524, d83916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d7524, d83916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d7525 q = 0) : d83917 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7525, d83917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d7525, d83917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d7526 q = 0) : d83918 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d7526, d83918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d7526, d83918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d7527 q = 0) : d83919 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d7527, d83919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d7527, d83919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d7561 q = 0) : d83945 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7561, d83945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7561, d83945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4711 q selected
  have h18 (q : Pattern) (selected : d737 q = 0) : d52414 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d737, d52414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d737, d52414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro314 q selected
  have h19 (q : Pattern) (selected : d7562 q = 0) : d83946 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7562, d83946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d7562, d83946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d7563 q = 0) : d83947 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7563, d83947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d7563, d83947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d7564 q = 0) : d83948 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d7564, d83948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d7564, d83948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d7565 q = 0) : d83949 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d7565, d83949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d7565, d83949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d7566 q = 0) : d83950 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d7566, d83950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d7566, d83950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro4713 (p : Pattern) (selected : d7572 p = 0) : d83956 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7567 q = 0) : d83951 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d7567, d83951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7567, d83951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4712 q selected
  have h2 (q : Pattern) (selected : d7568 q = 0) : d83952 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d7568, d83952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7568, d83952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7569 q = 0) : d83953 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d7569, d83953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7569, d83953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d7570 q = 0) : d83954 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d7570, d83954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7570, d83954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7571 q = 0) : d83955 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d7571, d83955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7571, d83955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7572 q = 0) : d83956 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d7572, d83956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7572, d83956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro4714 (p : Pattern) (selected : d7575 p = 0) : d83959 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d759 q = 0) : d52436 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d759, d52436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro318 q selected
    | true =>
      simp only [d759, d52436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro319 q selected
  have h2 (q : Pattern) (selected : d760 q = 0) : d52437 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d760, d52437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d760, d52437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d761 q = 0) : d52438 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d761, d52438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d761, d52438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d763 q = 0) : d52440 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d763, d52440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro319 q selected
    | true =>
      simp only [d763, d52440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro320 q selected
  have h5 (q : Pattern) (selected : d764 q = 0) : d52441 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d764, d52441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d764, d52441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d765 q = 0) : d52442 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d765, d52442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d765, d52442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d766 q = 0) : d52443 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d766, d52443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d766, d52443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7574 q = 0) : d83958 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7574, d83958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7574, d83958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d7575 q = 0) : d83959 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7575, d83959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7575, d83959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro4715 (p : Pattern) (selected : d7581 p = 0) : d83965 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7576 q = 0) : d83960 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7576, d83960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4714 q selected
    | true =>
      simp only [d7576, d83960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7577 q = 0) : d83961 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7577, d83961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7577, d83961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d774 q = 0) : d52451 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro322 q selected
    | true =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d775 q = 0) : d52452 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7578 q = 0) : d83962 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7578, d83962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7578, d83962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7579 q = 0) : d83963 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7579, d83963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7579, d83963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7580 q = 0) : d83964 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7580, d83964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7580, d83964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7581 q = 0) : d83965 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7581, d83965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7581, d83965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro4716 (p : Pattern) (selected : d7587 p = 0) : d83971 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7582 q = 0) : d83966 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7582, d83966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4715 q selected
    | true =>
      simp only [d7582, d83966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro324 q selected
  have h2 (q : Pattern) (selected : d7583 q = 0) : d83967 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7583, d83967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7583, d83967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7584 q = 0) : d83968 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7584, d83968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7584, d83968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7585 q = 0) : d83969 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7585, d83969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7585, d83969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7586 q = 0) : d83970 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7586, d83970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7586, d83970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7587 q = 0) : d83971 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7587, d83971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7587, d83971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro4717 (p : Pattern) (selected : d7590 p = 0) : d83974 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7576 q = 0) : d83960 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7576, d83960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4714 q selected
    | true =>
      simp only [d7576, d83960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7577 q = 0) : d83961 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7577, d83961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7577, d83961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d774 q = 0) : d52451 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro322 q selected
    | true =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d775 q = 0) : d52452 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7578 q = 0) : d83962 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7578, d83962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7578, d83962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7579 q = 0) : d83963 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7579, d83963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7579, d83963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7580 q = 0) : d83964 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7580, d83964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7580, d83964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7590 q = 0) : d83974 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7590, d83974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7590, d83974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro4718 (p : Pattern) (selected : d7596 p = 0) : d83980 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7582 q = 0) : d83966 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7582, d83966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4715 q selected
    | true =>
      simp only [d7582, d83966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro324 q selected
  have h2 (q : Pattern) (selected : d7583 q = 0) : d83967 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7583, d83967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7583, d83967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7584 q = 0) : d83968 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7584, d83968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7584, d83968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7585 q = 0) : d83969 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7585, d83969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7585, d83969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7586 q = 0) : d83970 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7586, d83970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7586, d83970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7591 q = 0) : d83975 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7591, d83975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4717 q selected
    | true =>
      simp only [d7591, d83975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro327 q selected
  have h7 (q : Pattern) (selected : d7592 q = 0) : d83976 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7592, d83976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7592, d83976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7593 q = 0) : d83977 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7593, d83977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7593, d83977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d7594 q = 0) : d83978 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7594, d83978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7594, d83978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d7595 q = 0) : d83979 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7595, d83979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7595, d83979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d7596 q = 0) : d83980 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7596, d83980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7596, d83980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro4719 (p : Pattern) (selected : d7601 p = 0) : d83985 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7576 q = 0) : d83960 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7576, d83960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4714 q selected
    | true =>
      simp only [d7576, d83960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7577 q = 0) : d83961 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7577, d83961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7577, d83961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d774 q = 0) : d52451 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro322 q selected
    | true =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d775 q = 0) : d52452 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7578 q = 0) : d83962 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7578, d83962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7578, d83962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7579 q = 0) : d83963 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7579, d83963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7579, d83963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7600 q = 0) : d83984 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7600, d83984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7600, d83984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7601 q = 0) : d83985 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7601, d83985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7601, d83985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro4720 (p : Pattern) (selected : d7608 p = 0) : d83992 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7576 q = 0) : d83960 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7576, d83960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4714 q selected
    | true =>
      simp only [d7576, d83960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7577 q = 0) : d83961 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7577, d83961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7577, d83961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d774 q = 0) : d52451 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro322 q selected
    | true =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d775 q = 0) : d52452 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7578 q = 0) : d83962 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7578, d83962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7578, d83962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7606 q = 0) : d83990 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7606, d83990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7606, d83990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7607 q = 0) : d83991 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7607, d83991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7607, d83991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7608 q = 0) : d83992 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7608, d83992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7608, d83992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro4721 (p : Pattern) (selected : d7613 p = 0) : d83997 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d840 q = 0) : d52517 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d840, d52517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro336 q selected
    | true =>
      simp only [d840, d52517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro318 q selected
  have h2 (q : Pattern) (selected : d841 q = 0) : d52518 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d841, d52518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d841, d52518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d842 q = 0) : d52519 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d842, d52519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d842, d52519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d759 q = 0) : d52436 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d759, d52436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro318 q selected
    | true =>
      simp only [d759, d52436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro319 q selected
  have h5 (q : Pattern) (selected : d760 q = 0) : d52437 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d760, d52437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d760, d52437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d761 q = 0) : d52438 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d761, d52438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d761, d52438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d843 q = 0) : d52520 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d843, d52520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d843, d52520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7612 q = 0) : d83996 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7612, d83996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7612, d83996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d7613 q = 0) : d83997 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7613, d83997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7613, d83997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro4722 (p : Pattern) (selected : d7619 p = 0) : d84003 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7614 q = 0) : d83998 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7614, d83998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4721 q selected
    | true =>
      simp only [d7614, d83998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7615 q = 0) : d83999 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7615, d83999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7615, d83999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7576 q = 0) : d83960 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7576, d83960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4714 q selected
    | true =>
      simp only [d7576, d83960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7577 q = 0) : d83961 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7577, d83961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7577, d83961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7616 q = 0) : d84000 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7616, d84000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7616, d84000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7617 q = 0) : d84001 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7617, d84001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7617, d84001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7618 q = 0) : d84002 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7618, d84002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7618, d84002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7619 q = 0) : d84003 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7619, d84003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7619, d84003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro4723 (p : Pattern) (selected : d7622 p = 0) : d83959 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d882 q = 0) : d52436 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d882, d52436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro343 q selected
    | true =>
      simp only [d882, d52436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro344 q selected
  have h2 (q : Pattern) (selected : d883 q = 0) : d52437 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d883, d52437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d883, d52437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d884 q = 0) : d52438 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d884, d52438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d884, d52438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d886 q = 0) : d52440 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d886, d52440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro344 q selected
    | true =>
      simp only [d886, d52440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro345 q selected
  have h5 (q : Pattern) (selected : d887 q = 0) : d52441 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d887, d52441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d887, d52441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d888 q = 0) : d52442 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d888, d52442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d888, d52442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d889 q = 0) : d52443 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d889, d52443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d889, d52443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7621 q = 0) : d83958 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7621, d83958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7621, d83958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d7622 q = 0) : d83959 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7622, d83959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7622, d83959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro4724 (p : Pattern) (selected : d7628 p = 0) : d83965 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7623 q = 0) : d83960 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7623, d83960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4723 q selected
    | true =>
      simp only [d7623, d83960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7624 q = 0) : d83961 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7624, d83961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7624, d83961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d897 q = 0) : d52451 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d897, d52451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro347 q selected
    | true =>
      simp only [d897, d52451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d898 q = 0) : d52452 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d898, d52452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d898, d52452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7625 q = 0) : d83962 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7625, d83962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7625, d83962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7626 q = 0) : d83963 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7626, d83963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7626, d83963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7627 q = 0) : d83964 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7627, d83964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7627, d83964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7628 q = 0) : d83965 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7628, d83965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7628, d83965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro4725 (p : Pattern) (selected : d7634 p = 0) : d84009 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7576 q = 0) : d83960 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7576, d83960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4714 q selected
    | true =>
      simp only [d7576, d83960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7577 q = 0) : d83961 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7577, d83961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7577, d83961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7631 q = 0) : d84006 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7631, d84006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7631, d84006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7632 q = 0) : d84007 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7632, d84007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7632, d84007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d7633 q = 0) : d84008 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7633, d84008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7633, d84008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d7634 q = 0) : d84009 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7634, d84009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7634, d84009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro4726 (p : Pattern) (selected : d7640 p = 0) : d84015 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7602 q = 0) : d83986 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7602, d83986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4719 q selected
    | true =>
      simp only [d7602, d83986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro330 q selected
  have h2 (q : Pattern) (selected : d7603 q = 0) : d83987 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7603, d83987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7603, d83987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7604 q = 0) : d83988 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7604, d83988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7604, d83988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7605 q = 0) : d83989 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7605, d83989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7605, d83989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7609 q = 0) : d83993 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7609, d83993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4720 q selected
    | true =>
      simp only [d7609, d83993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro332 q selected
  have h6 (q : Pattern) (selected : d7610 q = 0) : d83994 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7610, d83994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7610, d83994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7611 q = 0) : d83995 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7611, d83995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7611, d83995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7620 q = 0) : d84004 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7620, d84004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4722 q selected
    | true =>
      simp only [d7620, d84004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4715 q selected
  have h9 (q : Pattern) (selected : d7629 q = 0) : d83966 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7629, d83966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4724 q selected
    | true =>
      simp only [d7629, d83966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro349 q selected
  have h10 (q : Pattern) (selected : d7630 q = 0) : d84005 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7630, d84005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7630, d84005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d7635 q = 0) : d84010 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7635, d84010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4725 q selected
    | true =>
      simp only [d7635, d84010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d7636 q = 0) : d84011 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7636, d84011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d7636, d84011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d7637 q = 0) : d84012 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7637, d84012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d7637, d84012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d7638 q = 0) : d84013 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7638, d84013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7638, d84013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d7639 q = 0) : d84014 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7639, d84014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7639, d84014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d7640 q = 0) : d84015 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7640, d84015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7640, d84015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro4727 (p : Pattern) (selected : d7641 p = 0) : d84016 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7576 q = 0) : d83960 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7576, d83960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4714 q selected
    | true =>
      simp only [d7576, d83960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7577 q = 0) : d83961 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7577, d83961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7577, d83961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d774 q = 0) : d52451 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro322 q selected
    | true =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d775 q = 0) : d52452 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7578 q = 0) : d83962 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7578, d83962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7578, d83962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7579 q = 0) : d83963 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7579, d83963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7579, d83963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7600 q = 0) : d83984 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7600, d83984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7600, d83984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7641 q = 0) : d84016 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7641, d84016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7641, d84016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro4728 (p : Pattern) (selected : d7646 p = 0) : d84021 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7576 q = 0) : d83960 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7576, d83960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4714 q selected
    | true =>
      simp only [d7576, d83960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7577 q = 0) : d83961 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7577, d83961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7577, d83961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d774 q = 0) : d52451 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro322 q selected
    | true =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d775 q = 0) : d52452 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7578 q = 0) : d83962 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7578, d83962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7578, d83962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7606 q = 0) : d83990 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7606, d83990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7606, d83990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7607 q = 0) : d83991 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7607, d83991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7607, d83991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7646 q = 0) : d84021 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7646, d84021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7646, d84021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro4729 (p : Pattern) (selected : d7650 p = 0) : d84025 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7614 q = 0) : d83998 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7614, d83998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4721 q selected
    | true =>
      simp only [d7614, d83998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7615 q = 0) : d83999 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7615, d83999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7615, d83999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7576 q = 0) : d83960 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7576, d83960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4714 q selected
    | true =>
      simp only [d7576, d83960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7577 q = 0) : d83961 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7577, d83961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7577, d83961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7616 q = 0) : d84000 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7616, d84000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7616, d84000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7617 q = 0) : d84001 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7617, d84001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7617, d84001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7618 q = 0) : d84002 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7618, d84002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7618, d84002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7650 q = 0) : d84025 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7650, d84025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7650, d84025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro4730 (p : Pattern) (selected : d7652 p = 0) : d83974 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7623 q = 0) : d83960 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7623, d83960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4723 q selected
    | true =>
      simp only [d7623, d83960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7624 q = 0) : d83961 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7624, d83961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7624, d83961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d897 q = 0) : d52451 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d897, d52451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro347 q selected
    | true =>
      simp only [d897, d52451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d898 q = 0) : d52452 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d898, d52452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d898, d52452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7625 q = 0) : d83962 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7625, d83962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7625, d83962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7626 q = 0) : d83963 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7626, d83963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7626, d83963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7627 q = 0) : d83964 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7627, d83964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7627, d83964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7652 q = 0) : d83974 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7652, d83974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7652, d83974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro4731 (p : Pattern) (selected : d7655 p = 0) : d84028 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7576 q = 0) : d83960 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7576, d83960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4714 q selected
    | true =>
      simp only [d7576, d83960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7577 q = 0) : d83961 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7577, d83961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7577, d83961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7631 q = 0) : d84006 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7631, d84006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7631, d84006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7632 q = 0) : d84007 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7632, d84007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7632, d84007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d7633 q = 0) : d84008 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7633, d84008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7633, d84008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d7655 q = 0) : d84028 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7655, d84028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7655, d84028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4732 (p : Pattern) (selected : d7661 p = 0) : d84034 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7602 q = 0) : d83986 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7602, d83986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4719 q selected
    | true =>
      simp only [d7602, d83986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro330 q selected
  have h2 (q : Pattern) (selected : d7603 q = 0) : d83987 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7603, d83987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7603, d83987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7604 q = 0) : d83988 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7604, d83988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7604, d83988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7605 q = 0) : d83989 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7605, d83989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7605, d83989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7609 q = 0) : d83993 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7609, d83993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4720 q selected
    | true =>
      simp only [d7609, d83993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro332 q selected
  have h6 (q : Pattern) (selected : d7610 q = 0) : d83994 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7610, d83994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7610, d83994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7611 q = 0) : d83995 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7611, d83995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7611, d83995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7620 q = 0) : d84004 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7620, d84004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4722 q selected
    | true =>
      simp only [d7620, d84004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4715 q selected
  have h9 (q : Pattern) (selected : d7629 q = 0) : d83966 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7629, d83966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4724 q selected
    | true =>
      simp only [d7629, d83966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro349 q selected
  have h10 (q : Pattern) (selected : d7630 q = 0) : d84005 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7630, d84005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7630, d84005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d7635 q = 0) : d84010 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7635, d84010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4725 q selected
    | true =>
      simp only [d7635, d84010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d7636 q = 0) : d84011 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7636, d84011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d7636, d84011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d7637 q = 0) : d84012 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7637, d84012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d7637, d84012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d7638 q = 0) : d84013 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7638, d84013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7638, d84013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d7639 q = 0) : d84014 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7639, d84014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7639, d84014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d7642 q = 0) : d84017 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7642, d84017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4727 q selected
    | true =>
      simp only [d7642, d84017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro352 q selected
  have h17 (q : Pattern) (selected : d7643 q = 0) : d84018 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7643, d84018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7643, d84018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d7644 q = 0) : d84019 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7644, d84019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d7644, d84019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d7645 q = 0) : d84020 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7645, d84020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7645, d84020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d7647 q = 0) : d84022 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7647, d84022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4728 q selected
    | true =>
      simp only [d7647, d84022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro354 q selected
  have h21 (q : Pattern) (selected : d7648 q = 0) : d84023 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7648, d84023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7648, d84023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d7649 q = 0) : d84024 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7649, d84024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d7649, d84024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d7651 q = 0) : d84026 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7651, d84026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4729 q selected
    | true =>
      simp only [d7651, d84026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4717 q selected
  have h24 (q : Pattern) (selected : d7653 q = 0) : d83975 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7653, d83975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4730 q selected
    | true =>
      simp only [d7653, d83975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro357 q selected
  have h25 (q : Pattern) (selected : d7654 q = 0) : d84027 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7654, d84027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d7654, d84027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d7656 q = 0) : d84029 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7656, d84029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4731 q selected
    | true =>
      simp only [d7656, d84029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d7657 q = 0) : d84030 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7657, d84030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d7657, d84030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d7658 q = 0) : d84031 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7658, d84031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d7658, d84031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d7659 q = 0) : d84032 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7659, d84032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d7659, d84032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d7660 q = 0) : d84033 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7660, d84033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d7660, d84033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d7661 q = 0) : d84034 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7661, d84034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d7661, d84034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro4733 (p : Pattern) (selected : d7663 p = 0) : d84036 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7582 q = 0) : d83966 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7582, d83966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4715 q selected
    | true =>
      simp only [d7582, d83966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro324 q selected
  have h2 (q : Pattern) (selected : d7583 q = 0) : d83967 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7583, d83967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7583, d83967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7584 q = 0) : d83968 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7584, d83968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7584, d83968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7585 q = 0) : d83969 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7585, d83969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7585, d83969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7586 q = 0) : d83970 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7586, d83970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7586, d83970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d939 q = 0) : d52558 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d939, d52558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro324 q selected
    | true =>
      simp only [d939, d52558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d940 q = 0) : d52559 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d940, d52559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d940, d52559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d941 q = 0) : d52560 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d941, d52560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d941, d52560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d942 q = 0) : d52561 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d942, d52561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d942, d52561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d943 q = 0) : d52562 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d943, d52562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d943, d52562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d7663 q = 0) : d84036 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7663, d84036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7663, d84036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro4734 (p : Pattern) (selected : d7670 p = 0) : d84043 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7651 q = 0) : d84026 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7651, d84026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4729 q selected
    | true =>
      simp only [d7651, d84026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4717 q selected
  have h2 (q : Pattern) (selected : d7653 q = 0) : d83975 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7653, d83975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4730 q selected
    | true =>
      simp only [d7653, d83975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro357 q selected
  have h3 (q : Pattern) (selected : d7654 q = 0) : d84027 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7654, d84027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d7654, d84027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d7656 q = 0) : d84029 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7656, d84029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4731 q selected
    | true =>
      simp only [d7656, d84029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d7657 q = 0) : d84030 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7657, d84030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7657, d84030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d7658 q = 0) : d84031 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7658, d84031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7658, d84031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7668 q = 0) : d84041 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7668, d84041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7668, d84041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7669 q = 0) : d84042 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7669, d84042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7669, d84042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d7670 q = 0) : d84043 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7670, d84043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7670, d84043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro4735 (p : Pattern) (selected : d7677 p = 0) : d84050 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d977 q = 0) : d52596 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d977, d52596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro363 q selected
    | true =>
      simp only [d977, d52596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro364 q selected
  have h2 (q : Pattern) (selected : d978 q = 0) : d52597 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d978, d52597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d978, d52597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d979 q = 0) : d52598 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d979, d52598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d979, d52598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d982 q = 0) : d52601 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d982, d52601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro364 q selected
    | true =>
      simp only [d982, d52601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro365 q selected
  have h5 (q : Pattern) (selected : d983 q = 0) : d52602 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d983, d52602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d983, d52602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d984 q = 0) : d52603 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d984, d52603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d984, d52603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d985 q = 0) : d52604 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d985, d52604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d985, d52604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7676 q = 0) : d84049 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7676, d84049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7676, d84049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d7677 q = 0) : d84050 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7677, d84050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7677, d84050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro4736 (p : Pattern) (selected : d7681 p = 0) : d84054 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d982 q = 0) : d52601 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d982, d52601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro364 q selected
    | true =>
      simp only [d982, d52601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro365 q selected
  have h2 (q : Pattern) (selected : d983 q = 0) : d52602 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d983, d52602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d983, d52602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d984 q = 0) : d52603 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d984, d52603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d984, d52603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d987 q = 0) : d52606 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d987, d52606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro365 q selected
    | true =>
      simp only [d987, d52606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro366 q selected
  have h5 (q : Pattern) (selected : d988 q = 0) : d52607 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d52607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d988, d52607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d989 q = 0) : d52608 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, d52608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d989, d52608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d990 q = 0) : d52609 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d990, d52609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d990, d52609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7680 q = 0) : d84053 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7680, d84053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7680, d84053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d7681 q = 0) : d84054 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7681, d84054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7681, d84054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro4737 (p : Pattern) (selected : d7687 p = 0) : d84060 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7678 q = 0) : d84051 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7678, d84051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4735 q selected
    | true =>
      simp only [d7678, d84051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7679 q = 0) : d84052 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7679, d84052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7679, d84052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7682 q = 0) : d84055 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7682, d84055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4736 q selected
    | true =>
      simp only [d7682, d84055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7683 q = 0) : d84056 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7683, d84056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7683, d84056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7684 q = 0) : d84057 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7684, d84057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7684, d84057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7685 q = 0) : d84058 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7685, d84058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7685, d84058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7686 q = 0) : d84059 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7686, d84059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7686, d84059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7687 q = 0) : d84060 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7687, d84060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7687, d84060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro4738 (p : Pattern) (selected : d7691 p = 0) : d84064 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7682 q = 0) : d84055 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7682, d84055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4736 q selected
    | true =>
      simp only [d7682, d84055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7683 q = 0) : d84056 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7683, d84056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7683, d84056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1006 q = 0) : d52625 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1006, d52625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro370 q selected
    | true =>
      simp only [d1006, d52625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1007 q = 0) : d52626 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1007, d52626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1007, d52626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7688 q = 0) : d84061 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7688, d84061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7688, d84061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7689 q = 0) : d84062 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7689, d84062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7689, d84062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7690 q = 0) : d84063 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7690, d84063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7690, d84063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7691 q = 0) : d84064 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7691, d84064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7691, d84064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro4739 (p : Pattern) (selected : d7694 p = 0) : d84054 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1026 q = 0) : d52601 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1026, d52601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro372 q selected
    | true =>
      simp only [d1026, d52601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro373 q selected
  have h2 (q : Pattern) (selected : d1027 q = 0) : d52602 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1027, d52602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1027, d52602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1028 q = 0) : d52603 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1028, d52603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1028, d52603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1030 q = 0) : d52606 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1030, d52606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro373 q selected
    | true =>
      simp only [d1030, d52606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro374 q selected
  have h5 (q : Pattern) (selected : d1031 q = 0) : d52607 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1031, d52607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1031, d52607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1032 q = 0) : d52608 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1032, d52608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1032, d52608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d1033 q = 0) : d52609 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1033, d52609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1033, d52609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7693 q = 0) : d84053 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7693, d84053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7693, d84053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d7694 q = 0) : d84054 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7694, d84054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7694, d84054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro4740 (p : Pattern) (selected : d7700 p = 0) : d84064 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7695 q = 0) : d84055 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7695, d84055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4739 q selected
    | true =>
      simp only [d7695, d84055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7696 q = 0) : d84056 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7696, d84056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7696, d84056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1041 q = 0) : d52625 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1041, d52625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro376 q selected
    | true =>
      simp only [d1041, d52625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1042 q = 0) : d52626 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1042, d52626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1042, d52626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7697 q = 0) : d84061 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7697, d84061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7697, d84061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7698 q = 0) : d84062 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7698, d84062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7698, d84062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7699 q = 0) : d84063 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7699, d84063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7699, d84063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7700 q = 0) : d84064 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7700, d84064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7700, d84064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro4741 (p : Pattern) (selected : d7706 p = 0) : d84071 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7682 q = 0) : d84055 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7682, d84055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4736 q selected
    | true =>
      simp only [d7682, d84055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7683 q = 0) : d84056 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7683, d84056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7683, d84056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7703 q = 0) : d84068 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7703, d84068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7703, d84068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7704 q = 0) : d84069 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7704, d84069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7704, d84069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d7705 q = 0) : d84070 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7705, d84070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7705, d84070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d7706 q = 0) : d84071 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7706, d84071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7706, d84071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4742 (p : Pattern) (selected : d7712 p = 0) : d84077 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7692 q = 0) : d84065 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7692, d84065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4737 q selected
    | true =>
      simp only [d7692, d84065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4738 q selected
  have h2 (q : Pattern) (selected : d7701 q = 0) : d84066 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7701, d84066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4740 q selected
    | true =>
      simp only [d7701, d84066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro378 q selected
  have h3 (q : Pattern) (selected : d7702 q = 0) : d84067 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7702, d84067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d7702, d84067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d7707 q = 0) : d84072 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7707, d84072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4741 q selected
    | true =>
      simp only [d7707, d84072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d7708 q = 0) : d84073 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7708, d84073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7708, d84073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d7709 q = 0) : d84074 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7709, d84074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7709, d84074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7710 q = 0) : d84075 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7710, d84075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7710, d84075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7711 q = 0) : d84076 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7711, d84076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7711, d84076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d7712 q = 0) : d84077 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7712, d84077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7712, d84077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro4743 (p : Pattern) (selected : d7718 p = 0) : d84083 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7588 q = 0) : d83972 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7588, d83972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7588, d83972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4716 q selected
  have h2 (q : Pattern) (selected : d7589 q = 0) : d83973 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7589, d83973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d7589, d83973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d7597 q = 0) : d83981 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7597, d83981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4716 q selected
    | true =>
      simp only [d7597, d83981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4718 q selected
  have h4 (q : Pattern) (selected : d7598 q = 0) : d83982 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7598, d83982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7598, d83982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d7599 q = 0) : d83983 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7599, d83983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7599, d83983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7662 q = 0) : d84035 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7662, d84035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4726 q selected
    | true =>
      simp only [d7662, d84035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4732 q selected
  have h7 (q : Pattern) (selected : d7664 q = 0) : d84037 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7664, d84037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4733 q selected
    | true =>
      simp only [d7664, d84037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro360 q selected
  have h8 (q : Pattern) (selected : d7665 q = 0) : d84038 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7665, d84038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7665, d84038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d7666 q = 0) : d84039 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7666, d84039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7666, d84039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d7667 q = 0) : d84040 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d7667, d84040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7667, d84040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d7671 q = 0) : d84044 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7671, d84044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7671, d84044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4734 q selected
  have h12 (q : Pattern) (selected : d960 q = 0) : d52579 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d960, d52579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d960, d52579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro362 q selected
  have h13 (q : Pattern) (selected : d7672 q = 0) : d84045 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7672, d84045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d7672, d84045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d7673 q = 0) : d84046 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7673, d84046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d7673, d84046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d7674 q = 0) : d84047 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d7674, d84047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d7674, d84047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d7675 q = 0) : d84048 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d7675, d84048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d7675, d84048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d7713 q = 0) : d84078 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7713, d84078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7713, d84078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4742 q selected
  have h18 (q : Pattern) (selected : d1070 q = 0) : d52651 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1070, d52651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1070, d52651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro381 q selected
  have h19 (q : Pattern) (selected : d7714 q = 0) : d84079 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7714, d84079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d7714, d84079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d7715 q = 0) : d84080 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7715, d84080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d7715, d84080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d7716 q = 0) : d84081 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d7716, d84081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d7716, d84081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d7717 q = 0) : d84082 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d7717, d84082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d7717, d84082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d7718 q = 0) : d84083 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d7718, d84083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d7718, d84083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro4744 (p : Pattern) (selected : d7724 p = 0) : d84089 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7719 q = 0) : d84084 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d7719, d84084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7719, d84084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4743 q selected
  have h2 (q : Pattern) (selected : d7720 q = 0) : d84085 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d7720, d84085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7720, d84085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7721 q = 0) : d84086 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d7721, d84086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7721, d84086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d7722 q = 0) : d84087 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d7722, d84087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7722, d84087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7723 q = 0) : d84088 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d7723, d84088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7723, d84088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7724 q = 0) : d84089 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d7724, d84089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7724, d84089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro4745 (p : Pattern) (selected : d7728 p = 0) : d84093 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1129 q = 0) : d52710 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1129, d52710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro389 q selected
    | true =>
      simp only [d1129, d52710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro390 q selected
  have h2 (q : Pattern) (selected : d1130 q = 0) : d52711 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1130, d52711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1130, d52711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1131 q = 0) : d52712 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1131, d52712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1131, d52712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1142 q = 0) : d52723 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1142, d52723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro390 q selected
    | true =>
      simp only [d1142, d52723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro392 q selected
  have h5 (q : Pattern) (selected : d1143 q = 0) : d52724 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1143, d52724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1143, d52724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1144 q = 0) : d52725 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1144, d52725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1144, d52725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d1145 q = 0) : d52726 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1145, d52726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1145, d52726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7727 q = 0) : d84092 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7727, d84092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7727, d84092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d7728 q = 0) : d84093 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7728, d84093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7728, d84093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro4746 (p : Pattern) (selected : d7734 p = 0) : d84099 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7729 q = 0) : d84094 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7729, d84094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4745 q selected
    | true =>
      simp only [d7729, d84094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7730 q = 0) : d84095 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7730, d84095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7730, d84095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1153 q = 0) : d52734 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro394 q selected
    | true =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1154 q = 0) : d52735 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7731 q = 0) : d84096 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7731, d84096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7731, d84096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7732 q = 0) : d84097 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7732, d84097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7732, d84097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7733 q = 0) : d84098 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7733, d84098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7733, d84098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7734 q = 0) : d84099 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7734, d84099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7734, d84099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro4747 (p : Pattern) (selected : d7740 p = 0) : d84105 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7735 q = 0) : d84100 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7735, d84100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4746 q selected
    | true =>
      simp only [d7735, d84100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro396 q selected
  have h2 (q : Pattern) (selected : d7736 q = 0) : d84101 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7736, d84101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7736, d84101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7737 q = 0) : d84102 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7737, d84102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7737, d84102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7738 q = 0) : d84103 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7738, d84103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7738, d84103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7739 q = 0) : d84104 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7739, d84104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7739, d84104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7740 q = 0) : d84105 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7740, d84105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7740, d84105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro4748 (p : Pattern) (selected : d7743 p = 0) : d84108 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7729 q = 0) : d84094 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7729, d84094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4745 q selected
    | true =>
      simp only [d7729, d84094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7730 q = 0) : d84095 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7730, d84095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7730, d84095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1153 q = 0) : d52734 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro394 q selected
    | true =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1154 q = 0) : d52735 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7731 q = 0) : d84096 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7731, d84096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7731, d84096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7732 q = 0) : d84097 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7732, d84097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7732, d84097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7733 q = 0) : d84098 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7733, d84098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7733, d84098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7743 q = 0) : d84108 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7743, d84108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7743, d84108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro4749 (p : Pattern) (selected : d7749 p = 0) : d84114 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7735 q = 0) : d84100 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7735, d84100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4746 q selected
    | true =>
      simp only [d7735, d84100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro396 q selected
  have h2 (q : Pattern) (selected : d7736 q = 0) : d84101 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7736, d84101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7736, d84101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7737 q = 0) : d84102 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7737, d84102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7737, d84102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7738 q = 0) : d84103 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7738, d84103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7738, d84103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7739 q = 0) : d84104 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7739, d84104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7739, d84104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7744 q = 0) : d84109 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7744, d84109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4748 q selected
    | true =>
      simp only [d7744, d84109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro399 q selected
  have h7 (q : Pattern) (selected : d7745 q = 0) : d84110 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7745, d84110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7745, d84110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7746 q = 0) : d84111 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7746, d84111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7746, d84111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d7747 q = 0) : d84112 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7747, d84112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7747, d84112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d7748 q = 0) : d84113 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7748, d84113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7748, d84113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d7749 q = 0) : d84114 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7749, d84114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7749, d84114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
end NetHack.Soko22Hazard87
