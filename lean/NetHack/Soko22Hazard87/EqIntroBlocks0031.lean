import NetHack.Soko22Hazard87.EqIntroBlocks0030
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem eqIntro7750 (p : Pattern) (selected : d11212 p = 1) : d108901 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d11146 q = 1) : d11146 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d11155 q = 1) : d11155 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d11168 q = 1) : d11168 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d11193 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7748 q selected
    | true =>
      simp only [d11193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7749 q selected
  have h5 (q : Pattern) (selected : d11194 q = 1) : d108897 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11194, d108897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11194, d108897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11208 q = 1) : d11208 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d11209 q = 1) : d108898 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11209, d108898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11209, d108898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d11210 q = 1) : d108899 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11210, d108899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11210, d108899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d11211 q = 1) : d108900 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11211, d108900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d11211, d108900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d11212 q = 1) : d108901 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11212, d108901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11212, d108901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro7751 (p : Pattern) (selected : d11226 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d11179 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7746 q selected
    | true =>
      simp only [d11179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11180 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11183 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7747 q selected
    | true =>
      simp only [d11183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11184 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11185 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11186 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d11187 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d11226 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7752 (p : Pattern) (selected : d11227 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d11183 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7747 q selected
    | true =>
      simp only [d11183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11184 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11189 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11190 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11191 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d11227 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7753 (p : Pattern) (selected : d11236 p = 1) : d108906 p = 1 := by
  have h0 (q : Pattern) (selected : d11146 q = 1) : d11146 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d11155 q = 1) : d11155 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d11168 q = 1) : d11168 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d11193 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7748 q selected
    | true =>
      simp only [d11193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7749 q selected
  have h4 (q : Pattern) (selected : d11194 q = 1) : d108897 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11194, d108897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11194, d108897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11208 q = 1) : d11208 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d11209 q = 1) : d108898 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11209, d108898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11209, d108898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d11210 q = 1) : d108899 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11210, d108899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d11210, d108899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d11211 q = 1) : d108900 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11211, d108900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11211, d108900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d11218 q = 1) : d11218 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d11223 q = 1) : d11223 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d11225 q = 1) : d11225 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d11228 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7751 q selected
    | true =>
      simp only [d11228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7752 q selected
  have h13 (q : Pattern) (selected : d11229 q = 1) : d108902 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11229, d108902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d11229, d108902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d11232 q = 1) : d11232 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d11233 q = 1) : d108903 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11233, d108903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d11233, d108903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d11234 q = 1) : d108904 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11234, d108904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d11234, d108904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d11235 q = 1) : d108905 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11235, d108905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d11235, d108905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d11236 q = 1) : d108906 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11236, d108906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d11236, d108906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro7754 (p : Pattern) (selected : d11256 p = 1) : d108913 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d11225 q = 1) : d11225 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d11228 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7751 q selected
    | true =>
      simp only [d11228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7752 q selected
  have h3 (q : Pattern) (selected : d11229 q = 1) : d108902 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11229, d108902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d11229, d108902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d11232 q = 1) : d11232 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d11233 q = 1) : d108903 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11233, d108903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11233, d108903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11254 q = 1) : d108911 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11254, d108911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11254, d108911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d11255 q = 1) : d108912 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11255, d108912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11255, d108912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d11256 q = 1) : d108913 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11256, d108913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11256, d108913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7755 (p : Pattern) (selected : d11306 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d11297 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro65 q selected
    | true =>
      simp only [d11297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11298 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11299 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d11300 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro66 q selected
    | true =>
      simp only [d11300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11301 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11302 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d11303 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d11304 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d11305 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d11306 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d11306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro7756 (p : Pattern) (selected : d11310 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d11300 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro66 q selected
    | true =>
      simp only [d11300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11301 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11302 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d11304 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11309 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d11310 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7757 (p : Pattern) (selected : d11316 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d11307 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7755 q selected
    | true =>
      simp only [d11307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11308 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11311 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7756 q selected
    | true =>
      simp only [d11311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11312 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11313 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11314 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d11315 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d11316 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7758 (p : Pattern) (selected : d11320 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d11311 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7756 q selected
    | true =>
      simp only [d11311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11312 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11317 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11318 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11319 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d11320 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7759 (p : Pattern) (selected : d11340 p = 1) : d108923 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d11296 q = 1) : d11296 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d11321 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7757 q selected
    | true =>
      simp only [d11321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7758 q selected
  have h3 (q : Pattern) (selected : d11322 q = 1) : d108919 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11322, d108919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d11322, d108919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d11336 q = 1) : d11336 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d11337 q = 1) : d108920 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11337, d108920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11337, d108920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11338 q = 1) : d108921 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11338, d108921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11338, d108921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d11339 q = 1) : d108922 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11339, d108922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11339, d108922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d11340 q = 1) : d108923 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11340, d108923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11340, d108923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7760 (p : Pattern) (selected : d11357 p = 1) : d108929 p = 1 := by
  have h0 (q : Pattern) (selected : d11138 q = 1) : d11138 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d11237 q = 1) : d108907 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11237, d108907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7750 q selected
    | true =>
      simp only [d11237, d108907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7753 q selected
  have h2 (q : Pattern) (selected : d11250 q = 1) : d11250 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d11251 q = 1) : d108908 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11251, d108908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d11251, d108908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d11252 q = 1) : d108909 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d11252, d108909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11252, d108909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11253 q = 1) : d108910 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d11253, d108910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11253, d108910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d11257 q = 1) : d108914 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11257, d108914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11257, d108914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7754 q selected
  have h8 (q : Pattern) (selected : d11259 q = 1) : d11259 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d11260 q = 1) : d108915 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11260, d108915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11260, d108915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d11261 q = 1) : d108916 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d11261, d108916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d11261, d108916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d11262 q = 1) : d108917 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d11262, d108917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d11262, d108917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d11263 q = 1) : d108918 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d11263, d108918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11263, d108918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d11341 q = 1) : d108924 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11341, d108924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11341, d108924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7759 q selected
  have h14 (q : Pattern) (selected : d11352 q = 1) : d11352 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d11353 q = 1) : d108925 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11353, d108925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d11353, d108925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d11354 q = 1) : d108926 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d11354, d108926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d11354, d108926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d11355 q = 1) : d108927 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d11355, d108927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d11355, d108927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d11356 q = 1) : d108928 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d11356, d108928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d11356, d108928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d11357 q = 1) : d108929 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d11357, d108929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d11357, d108929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro7761 (p : Pattern) (selected : d11363 p = 1) : d108935 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d11358 q = 1) : d108930 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d11358, d108930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11358, d108930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7760 q selected
  have h2 (q : Pattern) (selected : d11359 q = 1) : d108931 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d11359, d108931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11359, d108931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11360 q = 1) : d108932 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d11360, d108932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11360, d108932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d11361 q = 1) : d108933 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d11361, d108933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11361, d108933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11362 q = 1) : d108934 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d11362, d108934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11362, d108934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11363 q = 1) : d108935 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d11363, d108935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11363, d108935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7762 (p : Pattern) (selected : d11448 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d11439 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro82 q selected
    | true =>
      simp only [d11439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11440 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11441 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d11442 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro83 q selected
    | true =>
      simp only [d11442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11443 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11444 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d11445 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d11446 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d11447 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d11448 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d11448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro7763 (p : Pattern) (selected : d11452 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d11442 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro83 q selected
    | true =>
      simp only [d11442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11443 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11444 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d11446 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11451 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d11452 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7764 (p : Pattern) (selected : d11458 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d11449 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7762 q selected
    | true =>
      simp only [d11449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11450 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11453 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7763 q selected
    | true =>
      simp only [d11453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11454 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11455 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11456 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d11457 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d11458 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7765 (p : Pattern) (selected : d11462 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d11453 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7763 q selected
    | true =>
      simp only [d11453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11454 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11459 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11460 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11461 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d11462 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7766 (p : Pattern) (selected : d11482 p = 1) : d108942 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d11416 q = 1) : d11416 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d11425 q = 1) : d11425 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d11438 q = 1) : d11438 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d11463 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7764 q selected
    | true =>
      simp only [d11463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7765 q selected
  have h5 (q : Pattern) (selected : d11464 q = 1) : d108938 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11464, d108938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11464, d108938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11478 q = 1) : d11478 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d11479 q = 1) : d108939 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11479, d108939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11479, d108939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d11480 q = 1) : d108940 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11480, d108940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11480, d108940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d11481 q = 1) : d108941 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11481, d108941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d11481, d108941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d11482 q = 1) : d108942 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11482, d108942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11482, d108942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro7767 (p : Pattern) (selected : d11496 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d11449 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7762 q selected
    | true =>
      simp only [d11449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11450 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11453 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7763 q selected
    | true =>
      simp only [d11453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11454 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11455 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11456 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d11457 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d11496 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7768 (p : Pattern) (selected : d11497 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d11453 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7763 q selected
    | true =>
      simp only [d11453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11454 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11459 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11460 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11461 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d11497 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7769 (p : Pattern) (selected : d11506 p = 1) : d108947 p = 1 := by
  have h0 (q : Pattern) (selected : d11416 q = 1) : d11416 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d11425 q = 1) : d11425 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d11438 q = 1) : d11438 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d11463 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7764 q selected
    | true =>
      simp only [d11463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7765 q selected
  have h4 (q : Pattern) (selected : d11464 q = 1) : d108938 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11464, d108938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11464, d108938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11478 q = 1) : d11478 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d11479 q = 1) : d108939 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11479, d108939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11479, d108939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d11480 q = 1) : d108940 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11480, d108940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d11480, d108940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d11481 q = 1) : d108941 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11481, d108941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11481, d108941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d11488 q = 1) : d11488 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d11493 q = 1) : d11493 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d11495 q = 1) : d11495 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d11498 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7767 q selected
    | true =>
      simp only [d11498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7768 q selected
  have h13 (q : Pattern) (selected : d11499 q = 1) : d108943 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11499, d108943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d11499, d108943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d11502 q = 1) : d11502 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d11503 q = 1) : d108944 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11503, d108944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d11503, d108944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d11504 q = 1) : d108945 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11504, d108945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d11504, d108945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d11505 q = 1) : d108946 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11505, d108946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d11505, d108946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d11506 q = 1) : d108947 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11506, d108947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d11506, d108947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro7770 (p : Pattern) (selected : d11526 p = 1) : d108954 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d11495 q = 1) : d11495 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d11498 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7767 q selected
    | true =>
      simp only [d11498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7768 q selected
  have h3 (q : Pattern) (selected : d11499 q = 1) : d108943 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11499, d108943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d11499, d108943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d11502 q = 1) : d11502 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d11503 q = 1) : d108944 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11503, d108944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11503, d108944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11524 q = 1) : d108952 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11524, d108952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11524, d108952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d11525 q = 1) : d108953 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11525, d108953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11525, d108953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d11526 q = 1) : d108954 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11526, d108954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11526, d108954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7771 (p : Pattern) (selected : d11576 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d11567 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro95 q selected
    | true =>
      simp only [d11567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11568 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11569 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d11570 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro96 q selected
    | true =>
      simp only [d11570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11571 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11572 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d11573 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d11574 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d11575 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d11576 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d11576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro7772 (p : Pattern) (selected : d11580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d11570 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro96 q selected
    | true =>
      simp only [d11570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11571 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11572 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d11574 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11579 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d11580 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7773 (p : Pattern) (selected : d11586 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d11577 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7771 q selected
    | true =>
      simp only [d11577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11578 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11581 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7772 q selected
    | true =>
      simp only [d11581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11582 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11583 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11584 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d11585 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d11586 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7774 (p : Pattern) (selected : d11590 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d11581 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7772 q selected
    | true =>
      simp only [d11581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11582 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11587 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11588 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11589 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d11590 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7775 (p : Pattern) (selected : d11610 p = 1) : d108964 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d11566 q = 1) : d11566 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d11591 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7773 q selected
    | true =>
      simp only [d11591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7774 q selected
  have h3 (q : Pattern) (selected : d11592 q = 1) : d108960 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11592, d108960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d11592, d108960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d11606 q = 1) : d11606 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d11607 q = 1) : d108961 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11607, d108961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11607, d108961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11608 q = 1) : d108962 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11608, d108962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11608, d108962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d11609 q = 1) : d108963 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11609, d108963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11609, d108963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d11610 q = 1) : d108964 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11610, d108964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11610, d108964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7776 (p : Pattern) (selected : d11627 p = 1) : d108970 p = 1 := by
  have h0 (q : Pattern) (selected : d11408 q = 1) : d11408 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d11507 q = 1) : d108948 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11507, d108948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7766 q selected
    | true =>
      simp only [d11507, d108948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7769 q selected
  have h2 (q : Pattern) (selected : d11520 q = 1) : d11520 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d11521 q = 1) : d108949 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11521, d108949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d11521, d108949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d11522 q = 1) : d108950 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d11522, d108950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11522, d108950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11523 q = 1) : d108951 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d11523, d108951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11523, d108951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d11527 q = 1) : d108955 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11527, d108955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11527, d108955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7770 q selected
  have h8 (q : Pattern) (selected : d11529 q = 1) : d11529 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d11530 q = 1) : d108956 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11530, d108956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11530, d108956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d11531 q = 1) : d108957 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d11531, d108957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d11531, d108957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d11532 q = 1) : d108958 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d11532, d108958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d11532, d108958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d11533 q = 1) : d108959 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d11533, d108959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11533, d108959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d11611 q = 1) : d108965 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11611, d108965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11611, d108965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7775 q selected
  have h14 (q : Pattern) (selected : d11622 q = 1) : d11622 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d11623 q = 1) : d108966 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11623, d108966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d11623, d108966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d11624 q = 1) : d108967 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d11624, d108967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d11624, d108967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d11625 q = 1) : d108968 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d11625, d108968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d11625, d108968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d11626 q = 1) : d108969 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d11626, d108969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d11626, d108969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d11627 q = 1) : d108970 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d11627, d108970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d11627, d108970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro7777 (p : Pattern) (selected : d11633 p = 1) : d108976 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d11628 q = 1) : d108971 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d11628, d108971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11628, d108971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7776 q selected
  have h2 (q : Pattern) (selected : d11629 q = 1) : d108972 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d11629, d108972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11629, d108972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11630 q = 1) : d108973 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d11630, d108973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11630, d108973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d11631 q = 1) : d108974 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d11631, d108974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11631, d108974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11632 q = 1) : d108975 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d11632, d108975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11632, d108975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11633 q = 1) : d108976 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d11633, d108976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11633, d108976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7778 (p : Pattern) (selected : d11719 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d11710 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro118 q selected
    | true =>
      simp only [d11710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11711 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11712 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d11713 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro119 q selected
    | true =>
      simp only [d11713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11714 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11715 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d11716 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d11717 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d11718 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d11719 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d11719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro7779 (p : Pattern) (selected : d11723 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d11713 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro119 q selected
    | true =>
      simp only [d11713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11714 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11715 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d11717 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11722 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d11723 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7780 (p : Pattern) (selected : d11729 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d11720 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7778 q selected
    | true =>
      simp only [d11720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11721 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11724 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7779 q selected
    | true =>
      simp only [d11724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11725 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11726 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11727 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d11728 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d11729 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7781 (p : Pattern) (selected : d11733 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d11724 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7779 q selected
    | true =>
      simp only [d11724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11725 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11730 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11731 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11732 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d11733 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7782 (p : Pattern) (selected : d11753 p = 1) : d108984 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d11687 q = 1) : d11687 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d11696 q = 1) : d11696 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d11709 q = 1) : d11709 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d11734 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7780 q selected
    | true =>
      simp only [d11734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7781 q selected
  have h5 (q : Pattern) (selected : d11735 q = 1) : d108980 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11735, d108980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11735, d108980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11749 q = 1) : d11749 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d11750 q = 1) : d108981 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11750, d108981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11750, d108981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d11751 q = 1) : d108982 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11751, d108982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11751, d108982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d11752 q = 1) : d108983 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11752, d108983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d11752, d108983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d11753 q = 1) : d108984 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11753, d108984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11753, d108984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro7783 (p : Pattern) (selected : d11767 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d11720 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7778 q selected
    | true =>
      simp only [d11720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11721 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11724 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7779 q selected
    | true =>
      simp only [d11724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11725 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11726 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11727 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d11728 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d11767 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7784 (p : Pattern) (selected : d11768 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d11724 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7779 q selected
    | true =>
      simp only [d11724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11725 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11730 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11731 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11732 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d11768 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7785 (p : Pattern) (selected : d11777 p = 1) : d108989 p = 1 := by
  have h0 (q : Pattern) (selected : d11687 q = 1) : d11687 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d11696 q = 1) : d11696 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d11709 q = 1) : d11709 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d11734 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7780 q selected
    | true =>
      simp only [d11734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7781 q selected
  have h4 (q : Pattern) (selected : d11735 q = 1) : d108980 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11735, d108980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11735, d108980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11749 q = 1) : d11749 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d11750 q = 1) : d108981 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11750, d108981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11750, d108981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d11751 q = 1) : d108982 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11751, d108982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d11751, d108982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d11752 q = 1) : d108983 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11752, d108983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11752, d108983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d11759 q = 1) : d11759 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d11764 q = 1) : d11764 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d11766 q = 1) : d11766 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d11769 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7783 q selected
    | true =>
      simp only [d11769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7784 q selected
  have h13 (q : Pattern) (selected : d11770 q = 1) : d108985 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11770, d108985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d11770, d108985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d11773 q = 1) : d11773 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d11774 q = 1) : d108986 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11774, d108986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d11774, d108986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d11775 q = 1) : d108987 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11775, d108987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d11775, d108987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d11776 q = 1) : d108988 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11776, d108988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d11776, d108988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d11777 q = 1) : d108989 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11777, d108989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d11777, d108989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro7786 (p : Pattern) (selected : d11797 p = 1) : d108996 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d11766 q = 1) : d11766 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d11769 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7783 q selected
    | true =>
      simp only [d11769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7784 q selected
  have h3 (q : Pattern) (selected : d11770 q = 1) : d108985 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11770, d108985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d11770, d108985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d11773 q = 1) : d11773 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d11774 q = 1) : d108986 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11774, d108986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11774, d108986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11795 q = 1) : d108994 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11795, d108994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11795, d108994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d11796 q = 1) : d108995 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11796, d108995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11796, d108995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d11797 q = 1) : d108996 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11797, d108996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11797, d108996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7787 (p : Pattern) (selected : d11847 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d11838 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro131 q selected
    | true =>
      simp only [d11838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11839 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11840 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d11841 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro132 q selected
    | true =>
      simp only [d11841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11842 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11843 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d11844 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d11845 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d11846 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d11847 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d11847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro7788 (p : Pattern) (selected : d11851 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d11841 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro132 q selected
    | true =>
      simp only [d11841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11842 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11843 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d11845 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11850 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d11851 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7789 (p : Pattern) (selected : d11857 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d11848 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7787 q selected
    | true =>
      simp only [d11848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11849 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11852 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7788 q selected
    | true =>
      simp only [d11852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11853 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11854 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11855 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d11856 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d11857 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7790 (p : Pattern) (selected : d11861 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d11852 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7788 q selected
    | true =>
      simp only [d11852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11853 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11858 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11859 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11860 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d11861 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7791 (p : Pattern) (selected : d11881 p = 1) : d109006 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d11837 q = 1) : d11837 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d11862 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7789 q selected
    | true =>
      simp only [d11862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7790 q selected
  have h3 (q : Pattern) (selected : d11863 q = 1) : d109002 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11863, d109002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d11863, d109002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d11877 q = 1) : d11877 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d11878 q = 1) : d109003 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11878, d109003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11878, d109003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11879 q = 1) : d109004 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11879, d109004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11879, d109004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d11880 q = 1) : d109005 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11880, d109005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11880, d109005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d11881 q = 1) : d109006 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11881, d109006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11881, d109006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7792 (p : Pattern) (selected : d11898 p = 1) : d109012 p = 1 := by
  have h0 (q : Pattern) (selected : d11679 q = 1) : d11679 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d11778 q = 1) : d108990 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11778, d108990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7782 q selected
    | true =>
      simp only [d11778, d108990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7785 q selected
  have h2 (q : Pattern) (selected : d11791 q = 1) : d11791 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d11792 q = 1) : d108991 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11792, d108991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d11792, d108991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d11793 q = 1) : d108992 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d11793, d108992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11793, d108992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11794 q = 1) : d108993 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d11794, d108993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11794, d108993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d11798 q = 1) : d108997 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11798, d108997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11798, d108997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7786 q selected
  have h8 (q : Pattern) (selected : d11800 q = 1) : d11800 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d11801 q = 1) : d108998 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11801, d108998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11801, d108998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d11802 q = 1) : d108999 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d11802, d108999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d11802, d108999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d11803 q = 1) : d109000 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d11803, d109000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d11803, d109000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d11804 q = 1) : d109001 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d11804, d109001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11804, d109001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d11882 q = 1) : d109007 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11882, d109007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11882, d109007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7791 q selected
  have h14 (q : Pattern) (selected : d11893 q = 1) : d11893 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d11894 q = 1) : d109008 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11894, d109008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d11894, d109008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d11895 q = 1) : d109009 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d11895, d109009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d11895, d109009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d11896 q = 1) : d109010 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d11896, d109010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d11896, d109010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d11897 q = 1) : d109011 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d11897, d109011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d11897, d109011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d11898 q = 1) : d109012 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d11898, d109012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d11898, d109012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro7793 (p : Pattern) (selected : d11904 p = 1) : d109018 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d11899 q = 1) : d109013 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d11899, d109013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11899, d109013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7792 q selected
  have h2 (q : Pattern) (selected : d11900 q = 1) : d109014 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d11900, d109014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11900, d109014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11901 q = 1) : d109015 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d11901, d109015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11901, d109015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d11902 q = 1) : d109016 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d11902, d109016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11902, d109016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11903 q = 1) : d109017 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d11903, d109017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11903, d109017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11904 q = 1) : d109018 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d11904, d109018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11904, d109018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7794 (p : Pattern) (selected : d11991 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d11982 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro155 q selected
    | true =>
      simp only [d11982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11983 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11984 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d11985 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro156 q selected
    | true =>
      simp only [d11985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11986 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11987 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d11988 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d11989 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d11990 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d11991 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d11991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro7795 (p : Pattern) (selected : d11995 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d11985 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro156 q selected
    | true =>
      simp only [d11985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11986 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11987 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d11989 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11994 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d11995 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7796 (p : Pattern) (selected : d12001 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d11992 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7794 q selected
    | true =>
      simp only [d11992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11993 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11996 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7795 q selected
    | true =>
      simp only [d11996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11997 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11998 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11999 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d12000 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d12000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d12001 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7797 (p : Pattern) (selected : d12005 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d11996 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7795 q selected
    | true =>
      simp only [d11996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11997 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d12002 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d12002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d12003 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d12003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d12004 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d12004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d12005 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7798 (p : Pattern) (selected : d12025 p = 1) : d109027 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d11959 q = 1) : d11959 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d11968 q = 1) : d11968 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d11981 q = 1) : d11981 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d12006 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7796 q selected
    | true =>
      simp only [d12006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7797 q selected
  have h5 (q : Pattern) (selected : d12007 q = 1) : d109023 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12007, d109023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d12007, d109023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d12021 q = 1) : d12021 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d12022 q = 1) : d109024 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12022, d109024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d12022, d109024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d12023 q = 1) : d109025 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12023, d109025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d12023, d109025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d12024 q = 1) : d109026 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12024, d109026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d12024, d109026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d12025 q = 1) : d109027 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12025, d109027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12025, d109027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro7799 (p : Pattern) (selected : d12039 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d11992 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7794 q selected
    | true =>
      simp only [d11992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11993 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11996 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7795 q selected
    | true =>
      simp only [d11996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11997 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11998 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11999 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d12000 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d12000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d12039 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d12039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7800 (p : Pattern) (selected : d12040 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d11996 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7795 q selected
    | true =>
      simp only [d11996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11997 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d12002 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d12002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d12003 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d12003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d12004 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d12004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d12040 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d12040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7801 (p : Pattern) (selected : d12049 p = 1) : d109032 p = 1 := by
  have h0 (q : Pattern) (selected : d11959 q = 1) : d11959 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d11968 q = 1) : d11968 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d11981 q = 1) : d11981 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d12006 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7796 q selected
    | true =>
      simp only [d12006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7797 q selected
  have h4 (q : Pattern) (selected : d12007 q = 1) : d109023 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12007, d109023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d12007, d109023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d12021 q = 1) : d12021 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d12022 q = 1) : d109024 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12022, d109024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d12022, d109024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d12023 q = 1) : d109025 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12023, d109025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d12023, d109025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d12024 q = 1) : d109026 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12024, d109026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12024, d109026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d12031 q = 1) : d12031 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d12036 q = 1) : d12036 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d12038 q = 1) : d12038 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d12041 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7799 q selected
    | true =>
      simp only [d12041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7800 q selected
  have h13 (q : Pattern) (selected : d12042 q = 1) : d109028 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12042, d109028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d12042, d109028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d12045 q = 1) : d12045 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d12046 q = 1) : d109029 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12046, d109029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d12046, d109029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d12047 q = 1) : d109030 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12047, d109030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d12047, d109030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d12048 q = 1) : d109031 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12048, d109031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d12048, d109031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d12049 q = 1) : d109032 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12049, d109032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d12049, d109032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro7802 (p : Pattern) (selected : d12069 p = 1) : d109039 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d12038 q = 1) : d12038 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d12041 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7799 q selected
    | true =>
      simp only [d12041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7800 q selected
  have h3 (q : Pattern) (selected : d12042 q = 1) : d109028 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12042, d109028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d12042, d109028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d12045 q = 1) : d12045 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d12046 q = 1) : d109029 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12046, d109029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d12046, d109029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d12067 q = 1) : d109037 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12067, d109037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12067, d109037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d12068 q = 1) : d109038 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12068, d109038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12068, d109038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d12069 q = 1) : d109039 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12069, d109039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12069, d109039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7803 (p : Pattern) (selected : d12119 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d12110 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro168 q selected
    | true =>
      simp only [d12110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d12111 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d12112 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d12113 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro169 q selected
    | true =>
      simp only [d12113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d12114 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d12115 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d12116 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d12116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d12117 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d12117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d12118 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d12118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d12119 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d12119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro7804 (p : Pattern) (selected : d12123 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d12113 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro169 q selected
    | true =>
      simp only [d12113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d12114 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d12115 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d12117 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d12117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d12122 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d12122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d12123 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d12123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7805 (p : Pattern) (selected : d12129 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d12120 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7803 q selected
    | true =>
      simp only [d12120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d12121 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d12124 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7804 q selected
    | true =>
      simp only [d12124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d12125 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d12126 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d12126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d12127 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d12127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d12128 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d12128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d12129 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d12129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7806 (p : Pattern) (selected : d12133 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d12124 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7804 q selected
    | true =>
      simp only [d12124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d12125 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d12130 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d12130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d12131 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d12131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d12132 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d12132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d12133 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d12133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7807 (p : Pattern) (selected : d12153 p = 1) : d109049 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d12109 q = 1) : d12109 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d12134 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7805 q selected
    | true =>
      simp only [d12134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7806 q selected
  have h3 (q : Pattern) (selected : d12135 q = 1) : d109045 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12135, d109045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d12135, d109045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d12149 q = 1) : d12149 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d12150 q = 1) : d109046 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12150, d109046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d12150, d109046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d12151 q = 1) : d109047 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12151, d109047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12151, d109047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d12152 q = 1) : d109048 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12152, d109048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12152, d109048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d12153 q = 1) : d109049 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12153, d109049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12153, d109049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7808 (p : Pattern) (selected : d12170 p = 1) : d109055 p = 1 := by
  have h0 (q : Pattern) (selected : d11951 q = 1) : d11951 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d12050 q = 1) : d109033 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12050, d109033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7798 q selected
    | true =>
      simp only [d12050, d109033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7801 q selected
  have h2 (q : Pattern) (selected : d12063 q = 1) : d12063 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d12064 q = 1) : d109034 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12064, d109034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d12064, d109034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d12065 q = 1) : d109035 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d12065, d109035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d12065, d109035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d12066 q = 1) : d109036 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d12066, d109036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12066, d109036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d12070 q = 1) : d109040 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12070, d109040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d12070, d109040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7802 q selected
  have h8 (q : Pattern) (selected : d12072 q = 1) : d12072 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d12073 q = 1) : d109041 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12073, d109041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d12073, d109041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d12074 q = 1) : d109042 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d12074, d109042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d12074, d109042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d12075 q = 1) : d109043 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d12075, d109043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d12075, d109043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d12076 q = 1) : d109044 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d12076, d109044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d12076, d109044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d12154 q = 1) : d109050 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12154, d109050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d12154, d109050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7807 q selected
  have h14 (q : Pattern) (selected : d12165 q = 1) : d12165 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d12166 q = 1) : d109051 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12166, d109051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d12166, d109051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d12167 q = 1) : d109052 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d12167, d109052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d12167, d109052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d12168 q = 1) : d109053 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d12168, d109053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d12168, d109053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d12169 q = 1) : d109054 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d12169, d109054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d12169, d109054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d12170 q = 1) : d109055 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d12170, d109055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d12170, d109055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro7809 (p : Pattern) (selected : d12176 p = 1) : d109061 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d12171 q = 1) : d109056 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d12171, d109056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12171, d109056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7808 q selected
  have h2 (q : Pattern) (selected : d12172 q = 1) : d109057 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d12172, d109057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12172, d109057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d12173 q = 1) : d109058 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d12173, d109058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12173, d109058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d12174 q = 1) : d109059 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d12174, d109059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12174, d109059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d12175 q = 1) : d109060 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d12175, d109060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12175, d109060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d12176 q = 1) : d109061 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d12176, d109061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12176, d109061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7810 (p : Pattern) (selected : d12182 p = 1) : d109067 p = 1 := by
  have h0 (q : Pattern) (selected : d11095 q = 1) : d108896 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d11095, d108896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7729 q selected
    | true =>
      simp only [d11095, d108896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7745 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d11364 q = 1) : d108936 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d11364, d108936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d11364, d108936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7761 q selected
  have h3 (q : Pattern) (selected : d11365 q = 1) : d108937 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d11365, d108937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11365, d108937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d11634 q = 1) : d108977 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d11634, d108977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d11634, d108977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7777 q selected
  have h5 (q : Pattern) (selected : d11635 q = 1) : d108978 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d11635, d108978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d11635, d108978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11636 q = 1) : d108979 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d11636, d108979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11636, d108979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d11905 q = 1) : d109019 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d11905, d109019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d11905, d109019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7793 q selected
  have h8 (q : Pattern) (selected : d11906 q = 1) : d109020 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d11906, d109020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d11906, d109020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d11907 q = 1) : d109021 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d11907, d109021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d11907, d109021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d11908 q = 1) : d109022 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d11908, d109022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11908, d109022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d12177 q = 1) : d109062 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d12177, d109062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d12177, d109062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7809 q selected
  have h12 (q : Pattern) (selected : d12178 q = 1) : d109063 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d12178, d109063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d12178, d109063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d12179 q = 1) : d109064 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d12179, d109064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d12179, d109064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d12180 q = 1) : d109065 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d12180, d109065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d12180, d109065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d12181 q = 1) : d109066 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d12181, d109066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d12181, d109066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d12182 q = 1) : d109067 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d12182, d109067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d12182, d109067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro7811 (p : Pattern) (selected : d12188 p = 1) : d109073 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d12183 q = 1) : d109068 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d12183, d109068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7810 q selected
    | true =>
      simp only [d12183, d109068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d12184 q = 1) : d109069 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d12184, d109069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d12184, d109069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d12185 q = 1) : d109070 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d12185, d109070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d12185, d109070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d12186 q = 1) : d109071 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d12186, d109071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d12186, d109071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d12187 q = 1) : d109072 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d12187, d109072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d12187, d109072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d12188 q = 1) : d109073 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d12188, d109073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d12188, d109073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7812 (p : Pattern) (selected : d12194 p = 1) : d109079 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d12189 q = 1) : d109074 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d12189, d109074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7811 q selected
    | true =>
      simp only [d12189, d109074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d12190 q = 1) : d109075 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d12190, d109075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d12190, d109075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d12191 q = 1) : d109076 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d12191, d109076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d12191, d109076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d12192 q = 1) : d109077 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d12192, d109077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d12192, d109077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d12193 q = 1) : d109078 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d12193, d109078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d12193, d109078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d12194 q = 1) : d109079 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d12194, d109079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d12194, d109079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7813 (p : Pattern) (selected : d12200 p = 1) : d109085 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d12195 q = 1) : d109080 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d12195, d109080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7812 q selected
    | true =>
      simp only [d12195, d109080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d12196 q = 1) : d109081 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d12196, d109081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d12196, d109081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d12197 q = 1) : d109082 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d12197, d109082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d12197, d109082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d12198 q = 1) : d109083 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d12198, d109083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d12198, d109083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d12199 q = 1) : d109084 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d12199, d109084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d12199, d109084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d12200 q = 1) : d109085 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d12200, d109085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d12200, d109085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7814 (p : Pattern) (selected : d12206 p = 1) : d109091 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d12201 q = 1) : d109086 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d12201, d109086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7813 q selected
    | true =>
      simp only [d12201, d109086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d12202 q = 1) : d109087 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d12202, d109087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d12202, d109087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d12203 q = 1) : d109088 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d12203, d109088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d12203, d109088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d12204 q = 1) : d109089 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d12204, d109089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d12204, d109089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d12205 q = 1) : d109090 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d12205, d109090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d12205, d109090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d12206 q = 1) : d109091 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d12206, d109091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d12206, d109091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7815 (p : Pattern) (selected : d12212 p = 1) : d109097 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d12207 q = 1) : d109092 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d12207, d109092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7814 q selected
    | true =>
      simp only [d12207, d109092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d12208 q = 1) : d109093 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d12208, d109093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d12208, d109093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d12209 q = 1) : d109094 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d12209, d109094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d12209, d109094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d12210 q = 1) : d109095 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d12210, d109095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d12210, d109095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d12211 q = 1) : d109096 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d12211, d109096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d12211, d109096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d12212 q = 1) : d109097 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d12212, d109097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d12212, d109097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7816 (p : Pattern) (selected : d12218 p = 1) : d109103 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d12213 q = 1) : d109098 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d12213, d109098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7815 q selected
    | true =>
      simp only [d12213, d109098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d12214 q = 1) : d109099 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d12214, d109099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d12214, d109099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d12215 q = 1) : d109100 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d12215, d109100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d12215, d109100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d12216 q = 1) : d109101 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d12216, d109101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d12216, d109101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d12217 q = 1) : d109102 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d12217, d109102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d12217, d109102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d12218 q = 1) : d109103 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d12218, d109103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d12218, d109103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7817 (p : Pattern) (selected : d12224 p = 1) : d109109 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d12219 q = 1) : d109104 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d12219, d109104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7816 q selected
    | true =>
      simp only [d12219, d109104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d12220 q = 1) : d109105 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d12220, d109105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d12220, d109105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d12221 q = 1) : d109106 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d12221, d109106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d12221, d109106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d12222 q = 1) : d109107 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d12222, d109107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d12222, d109107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d12223 q = 1) : d109108 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d12223, d109108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d12223, d109108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d12224 q = 1) : d109109 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d12224, d109109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d12224, d109109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7818 (p : Pattern) (selected : d7241 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d145 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro664 q selected
    | true =>
      simp only [d145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro646 q selected
  have h2 (q : Pattern) (selected : d146 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d147 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d31 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro646 q selected
    | true =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d32 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d33 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d148 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7240 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d7241 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro7819 (p : Pattern) (selected : d7247 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7242 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7818 q selected
    | true =>
      simp only [d7242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7243 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d37 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro647 q selected
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d38 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7244 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7245 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7246 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7247 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7820 (p : Pattern) (selected : d7253 p = 2) : d104 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d117 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro660 q selected
    | true =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d119 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d120 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d124 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro661 q selected
    | true =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d125 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d126 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7248 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7819 q selected
    | true =>
      simp only [d7248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro648 q selected
  have h9 (q : Pattern) (selected : d188 q = 2) : d43 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d188, d43, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro671 q selected
    | true =>
      simp only [d188, d43, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d7249 q = 2) : d100 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7249, d100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7249, d100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d43 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro648 q selected
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d44 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d7250 q = 2) : d101 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7250, d101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d7250, d101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d7251 q = 2) : d102 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7251, d102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7251, d102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d7252 q = 2) : d103 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7252, d103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7252, d103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d7253 q = 2) : d104 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7253, d104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7253, d104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro7821 (p : Pattern) (selected : d7254 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7242 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7818 q selected
    | true =>
      simp only [d7242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7243 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d37 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro647 q selected
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d38 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7244 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7245 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7246 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7254 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7822 (p : Pattern) (selected : d7260 p = 2) : d111 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d117 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro660 q selected
    | true =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d119 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d120 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d124 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro661 q selected
    | true =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d125 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d126 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7248 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7819 q selected
    | true =>
      simp only [d7248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro648 q selected
  have h9 (q : Pattern) (selected : d188 q = 2) : d43 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d188, d43, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro671 q selected
    | true =>
      simp only [d188, d43, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d7249 q = 2) : d100 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7249, d100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7249, d100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d43 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro648 q selected
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d44 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d7250 q = 2) : d101 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7250, d101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d7250, d101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d7251 q = 2) : d102 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7251, d102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7251, d102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d7252 q = 2) : d103 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7252, d103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7252, d103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d195 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro673 q selected
    | true =>
      simp only [d195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d196 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d197 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d198 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d200 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro674 q selected
    | true =>
      simp only [d200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d201 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d202 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d7255 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7821 q selected
    | true =>
      simp only [d7255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro650 q selected
  have h24 (q : Pattern) (selected : d206 q = 2) : d50 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d206, d50, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro676 q selected
    | true =>
      simp only [d206, d50, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h25 (q : Pattern) (selected : d7256 q = 2) : d107 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7256, d107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d7256, d107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d50 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro650 q selected
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d51 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d7257 q = 2) : d108 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7257, d108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d7257, d108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d7258 q = 2) : d109 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7258, d109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d7258, d109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d7259 q = 2) : d110 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7259, d110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d7259, d110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d7260 q = 2) : d111 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7260, d111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d7260, d111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro7823 (p : Pattern) (selected : d7267 p = 2) : d406 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7255 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7821 q selected
    | true =>
      simp only [d7255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro650 q selected
  have h2 (q : Pattern) (selected : d206 q = 2) : d50 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d206, d50, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro676 q selected
    | true =>
      simp only [d206, d50, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d7256 q = 2) : d107 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7256, d107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d7256, d107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d50 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro650 q selected
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d51 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d7257 q = 2) : d108 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7257, d108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7257, d108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7265 q = 2) : d109 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7265, d109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7265, d109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7266 q = 2) : d110 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7266, d110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7266, d110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d7267 q = 2) : d406 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7267, d406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7267, d406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro7824 (p : Pattern) (selected : d7274 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d232 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro680 q selected
    | true =>
      simp only [d232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro653 q selected
  have h2 (q : Pattern) (selected : d233 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d234 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d72 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro653 q selected
    | true =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d73 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d74 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d235 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7273 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d7274 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro7825 (p : Pattern) (selected : d7280 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7275 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7824 q selected
    | true =>
      simp only [d7275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7276 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d78 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro654 q selected
    | true =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d79 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7277 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7278 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7279 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7280 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7826 (p : Pattern) (selected : d7286 p = 2) : d462 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7281 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7825 q selected
    | true =>
      simp only [d7281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro655 q selected
  have h2 (q : Pattern) (selected : d263 q = 2) : d84 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263, d84, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro685 q selected
    | true =>
      simp only [d263, d84, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d7282 q = 2) : d458 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7282, d458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d7282, d458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d84 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro655 q selected
    | true =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d85 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d7283 q = 2) : d459 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7283, d459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7283, d459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7284 q = 2) : d460 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7284, d460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7284, d460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7285 q = 2) : d461 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7285, d461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7285, d461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d7286 q = 2) : d462 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7286, d462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7286, d462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro7827 (p : Pattern) (selected : d7292 p = 2) : d53647 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d105 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro658 q selected
  have h2 (q : Pattern) (selected : d106 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d112 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro658 q selected
    | true =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro659 q selected
  have h4 (q : Pattern) (selected : d113 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d114 q = 2) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7261 q = 2) : d112 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7261, d112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7820 q selected
    | true =>
      simp only [d7261, d112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7822 q selected
  have h7 (q : Pattern) (selected : d214 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro678 q selected
    | true =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7262 q = 2) : d113 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7262, d113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7262, d113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d7263 q = 2) : d53637 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7263, d53637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7263, d53637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d7264 q = 2) : d53638 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d7264, d53638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7264, d53638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d7268 q = 2) : d407 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7268, d407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7268, d407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7823 q selected
  have h12 (q : Pattern) (selected : d7269 q = 2) : d53639 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7269, d53639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d7269, d53639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d7270 q = 2) : d53640 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7270, d53640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d7270, d53640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d7271 q = 2) : d53641 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d7271, d53641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d7271, d53641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d7272 q = 2) : d53642 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d7272, d53642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d7272, d53642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d7287 q = 2) : d463 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7287, d463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7287, d463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7826 q selected
  have h17 (q : Pattern) (selected : d7288 q = 2) : d53643 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7288, d53643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d7288, d53643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d7289 q = 2) : d53644 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7289, d53644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d7289, d53644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d7290 q = 2) : d53645 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d7290, d53645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d7290, d53645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d7291 q = 2) : d53646 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d7291, d53646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d7291, d53646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d7292 q = 2) : d53647 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d7292, d53647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d7292, d53647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro7828 (p : Pattern) (selected : d7302 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7248 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7819 q selected
    | true =>
      simp only [d7248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro648 q selected
  have h2 (q : Pattern) (selected : d7298 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7299 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7300 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7301 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7302 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7829 (p : Pattern) (selected : d7309 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7248 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7819 q selected
    | true =>
      simp only [d7248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro648 q selected
  have h2 (q : Pattern) (selected : d7298 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7299 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7300 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7301 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7255 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7821 q selected
    | true =>
      simp only [d7255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro650 q selected
  have h7 (q : Pattern) (selected : d7305 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7306 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d7307 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d7308 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d7309 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro7830 (p : Pattern) (selected : d7314 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7242 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7818 q selected
    | true =>
      simp only [d7242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7243 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d37 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro647 q selected
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d38 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7244 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7245 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7313 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7314 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7831 (p : Pattern) (selected : d7321 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7242 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7818 q selected
    | true =>
      simp only [d7242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7243 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d37 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro647 q selected
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d38 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7244 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7319 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7320 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7321 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7832 (p : Pattern) (selected : d7326 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d325 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro694 q selected
    | true =>
      simp only [d325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro664 q selected
  have h2 (q : Pattern) (selected : d326 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d327 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d145 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro664 q selected
    | true =>
      simp only [d145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro646 q selected
  have h5 (q : Pattern) (selected : d146 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d147 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d328 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7325 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d7326 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro7833 (p : Pattern) (selected : d7332 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7327 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7832 q selected
    | true =>
      simp only [d7327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7328 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7242 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7818 q selected
    | true =>
      simp only [d7242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7243 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7329 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7330 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7331 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7332 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7834 (p : Pattern) (selected : d7335 p = 2) : d7241 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d356 q = 2) : d145 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d356, d145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro699 q selected
    | true =>
      simp only [d356, d145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro669 q selected
  have h2 (q : Pattern) (selected : d357 q = 2) : d146 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d357, d146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d357, d146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d358 q = 2) : d147 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d358, d147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d358, d147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d176 q = 2) : d31 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176, d31, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro669 q selected
    | true =>
      simp only [d176, d31, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d177 q = 2) : d32 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d177, d32, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177, d32, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d178 q = 2) : d33 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d178, d33, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d178, d33, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d359 q = 2) : d148 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d359, d148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359, d148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7334 q = 2) : d7240 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7334, d7240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7334, d7240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d7335 q = 2) : d7241 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7335, d7241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7335, d7241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro7835 (p : Pattern) (selected : d7341 p = 2) : d7247 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7336 q = 2) : d7242 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7336, d7242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7834 q selected
    | true =>
      simp only [d7336, d7242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7337 q = 2) : d7243 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7337, d7243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7337, d7243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182 q = 2) : d37 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182, d37, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro670 q selected
    | true =>
      simp only [d182, d37, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d183 q = 2) : d38 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d183, d38, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d183, d38, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7338 q = 2) : d7244 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7338, d7244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7338, d7244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7339 q = 2) : d7245 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7339, d7245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7339, d7245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7340 q = 2) : d7246 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7340, d7246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7340, d7246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7341 q = 2) : d7247 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7341, d7247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7341, d7247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7836 (p : Pattern) (selected : d7347 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7242 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7818 q selected
    | true =>
      simp only [d7242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7243 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7344 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7345 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d7346 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d7347 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7837 (p : Pattern) (selected : d7353 p = 2) : d7302 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7315 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7830 q selected
    | true =>
      simp only [d7315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro660 q selected
  have h2 (q : Pattern) (selected : d7316 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7317 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7318 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7322 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7831 q selected
    | true =>
      simp only [d7322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro661 q selected
  have h6 (q : Pattern) (selected : d7323 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7324 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7333 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7833 q selected
    | true =>
      simp only [d7333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7819 q selected
  have h9 (q : Pattern) (selected : d7342 q = 2) : d7248 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7342, d7248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7835 q selected
    | true =>
      simp only [d7342, d7248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro671 q selected
  have h10 (q : Pattern) (selected : d7343 q = 2) : d7298 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7343, d7298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7343, d7298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d7348 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7836 q selected
    | true =>
      simp only [d7348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d7349 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d7349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d7350 q = 2) : d7299 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7350, d7299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d7350, d7299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d7351 q = 2) : d7300 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7351, d7300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7351, d7300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d7352 q = 2) : d7301 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7352, d7301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7352, d7301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d7353 q = 2) : d7302 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7353, d7302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7353, d7302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro7838 (p : Pattern) (selected : d7354 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7242 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7818 q selected
    | true =>
      simp only [d7242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7243 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d37 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro647 q selected
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d38 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7244 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7245 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7313 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7354 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7839 (p : Pattern) (selected : d7359 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7242 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7818 q selected
    | true =>
      simp only [d7242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7243 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d37 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro647 q selected
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d38 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7244 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7319 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7320 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7359 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7840 (p : Pattern) (selected : d7363 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7327 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7832 q selected
    | true =>
      simp only [d7327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7328 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7242 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7818 q selected
    | true =>
      simp only [d7242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7243 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7329 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7330 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7331 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7363 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7841 (p : Pattern) (selected : d7365 p = 2) : d7254 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7336 q = 2) : d7242 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7336, d7242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7834 q selected
    | true =>
      simp only [d7336, d7242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7337 q = 2) : d7243 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7337, d7243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7337, d7243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182 q = 2) : d37 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182, d37, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro670 q selected
    | true =>
      simp only [d182, d37, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d183 q = 2) : d38 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d183, d38, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d183, d38, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7338 q = 2) : d7244 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7338, d7244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7338, d7244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7339 q = 2) : d7245 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7339, d7245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7339, d7245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7340 q = 2) : d7246 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7340, d7246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7340, d7246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7365 q = 2) : d7254 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7365, d7254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7365, d7254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7842 (p : Pattern) (selected : d7368 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7242 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7818 q selected
    | true =>
      simp only [d7242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7243 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7344 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7345 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d7346 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d7368 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7843 (p : Pattern) (selected : d7374 p = 2) : d7309 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7315 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7830 q selected
    | true =>
      simp only [d7315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro660 q selected
  have h2 (q : Pattern) (selected : d7316 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7317 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7318 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7322 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7831 q selected
    | true =>
      simp only [d7322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro661 q selected
  have h6 (q : Pattern) (selected : d7323 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7324 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7333 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7833 q selected
    | true =>
      simp only [d7333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7819 q selected
  have h9 (q : Pattern) (selected : d7342 q = 2) : d7248 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7342, d7248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7835 q selected
    | true =>
      simp only [d7342, d7248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro671 q selected
  have h10 (q : Pattern) (selected : d7343 q = 2) : d7298 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7343, d7298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7343, d7298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d7348 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7836 q selected
    | true =>
      simp only [d7348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d7349 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d7349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d7350 q = 2) : d7299 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7350, d7299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d7350, d7299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d7351 q = 2) : d7300 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7351, d7300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7351, d7300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d7352 q = 2) : d7301 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7352, d7301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7352, d7301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d7355 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7838 q selected
    | true =>
      simp only [d7355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro673 q selected
  have h17 (q : Pattern) (selected : d7356 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d7357 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d7357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d7358 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d7360 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7839 q selected
    | true =>
      simp only [d7360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro674 q selected
  have h21 (q : Pattern) (selected : d7361 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d7362 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d7362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d7364 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7840 q selected
    | true =>
      simp only [d7364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7821 q selected
  have h24 (q : Pattern) (selected : d7366 q = 2) : d7255 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7366, d7255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7841 q selected
    | true =>
      simp only [d7366, d7255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro676 q selected
  have h25 (q : Pattern) (selected : d7367 q = 2) : d7305 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7367, d7305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d7367, d7305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d7369 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7842 q selected
    | true =>
      simp only [d7369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d7370 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d7370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d7371 q = 2) : d7306 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7371, d7306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d7371, d7306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d7372 q = 2) : d7307 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7372, d7307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d7372, d7307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d7373 q = 2) : d7308 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7373, d7308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d7373, d7308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d7374 q = 2) : d7309 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7374, d7309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d7374, d7309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro7844 (p : Pattern) (selected : d7376 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7248 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7819 q selected
    | true =>
      simp only [d7248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro648 q selected
  have h2 (q : Pattern) (selected : d7298 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7299 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7300 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7301 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d43 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro648 q selected
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d100 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d101 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d102 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d103 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d7376 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro7845 (p : Pattern) (selected : d7383 p = 2) : d99199 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7364 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7840 q selected
    | true =>
      simp only [d7364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7821 q selected
  have h2 (q : Pattern) (selected : d7366 q = 2) : d7255 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7366, d7255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7841 q selected
    | true =>
      simp only [d7366, d7255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro676 q selected
  have h3 (q : Pattern) (selected : d7367 q = 2) : d7305 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7367, d7305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d7367, d7305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d7369 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7842 q selected
    | true =>
      simp only [d7369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d7370 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d7371 q = 2) : d7306 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7371, d7306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7371, d7306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7381 q = 2) : d7307 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7381, d7307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7381, d7307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7382 q = 2) : d7308 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7382, d7308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7382, d7308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d7383 q = 2) : d99199 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7383, d99199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7383, d99199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro7846 (p : Pattern) (selected : d7390 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d418 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro711 q selected
    | true =>
      simp only [d418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro680 q selected
  have h2 (q : Pattern) (selected : d419 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d420 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro680 q selected
    | true =>
      simp only [d232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro653 q selected
  have h5 (q : Pattern) (selected : d233 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d234 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d421 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7389 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d7390 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro7847 (p : Pattern) (selected : d7396 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7391 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7846 q selected
    | true =>
      simp only [d7391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7392 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7275 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7824 q selected
    | true =>
      simp only [d7275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7276 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7393 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7394 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7395 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7396 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7848 (p : Pattern) (selected : d7399 p = 2) : d7274 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d437 q = 2) : d232 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d437, d232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro714 q selected
    | true =>
      simp only [d437, d232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro683 q selected
  have h2 (q : Pattern) (selected : d438 q = 2) : d233 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d438, d233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d438, d233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d439 q = 2) : d234 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d439, d234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d439, d234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d251 q = 2) : d72 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d251, d72, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro683 q selected
    | true =>
      simp only [d251, d72, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d252 q = 2) : d73 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d252, d73, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d252, d73, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d253 q = 2) : d74 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d253, d74, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d253, d74, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d440 q = 2) : d235 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d440, d235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d440, d235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7398 q = 2) : d7273 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7398, d7273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7398, d7273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d7399 q = 2) : d7274 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7399, d7274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7399, d7274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro7849 (p : Pattern) (selected : d7405 p = 2) : d7280 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7400 q = 2) : d7275 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7400, d7275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7848 q selected
    | true =>
      simp only [d7400, d7275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7401 q = 2) : d7276 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7401, d7276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7401, d7276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d257 q = 2) : d78 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d257, d78, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro684 q selected
    | true =>
      simp only [d257, d78, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d258 q = 2) : d79 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d258, d79, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d258, d79, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7402 q = 2) : d7277 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7402, d7277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7402, d7277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7403 q = 2) : d7278 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7403, d7278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7403, d7278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7404 q = 2) : d7279 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7404, d7279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7404, d7279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7405 q = 2) : d7280 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7405, d7280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7405, d7280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7850 (p : Pattern) (selected : d7411 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7275 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7824 q selected
    | true =>
      simp only [d7275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7276 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7408 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7409 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d7410 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d7411 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7851 (p : Pattern) (selected : d7417 p = 2) : d99209 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7397 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7847 q selected
    | true =>
      simp only [d7397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7825 q selected
  have h2 (q : Pattern) (selected : d7406 q = 2) : d7281 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7406, d7281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7849 q selected
    | true =>
      simp only [d7406, d7281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro685 q selected
  have h3 (q : Pattern) (selected : d7407 q = 2) : d99205 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7407, d99205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d7407, d99205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d7412 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7850 q selected
    | true =>
      simp only [d7412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d7413 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d7414 q = 2) : d99206 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7414, d99206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7414, d99206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7415 q = 2) : d99207 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7415, d99207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7415, d99207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7416 q = 2) : d99208 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7416, d99208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7416, d99208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d7417 q = 2) : d99209 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7417, d99209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7417, d99209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro7852 (p : Pattern) (selected : d7423 p = 2) : d99215 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7303 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7828 q selected
  have h2 (q : Pattern) (selected : d7304 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d7304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d7310 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7828 q selected
    | true =>
      simp only [d7310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7829 q selected
  have h4 (q : Pattern) (selected : d7311 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d7312 q = 2) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7375 q = 2) : d7310 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7375, d7310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7837 q selected
    | true =>
      simp only [d7375, d7310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7843 q selected
  have h7 (q : Pattern) (selected : d7377 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7844 q selected
    | true =>
      simp only [d7377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro659 q selected
  have h8 (q : Pattern) (selected : d7378 q = 2) : d7311 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7378, d7311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7378, d7311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d7379 q = 2) : d99197 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7379, d99197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7379, d99197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d7380 q = 2) : d99198 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d7380, d99198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7380, d99198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d7384 q = 2) : d99200 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7384, d99200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7384, d99200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7845 q selected
  have h12 (q : Pattern) (selected : d407 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro710 q selected
  have h13 (q : Pattern) (selected : d7385 q = 2) : d99201 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7385, d99201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d7385, d99201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d7386 q = 2) : d99202 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7386, d99202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d7386, d99202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d7387 q = 2) : d99203 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d7387, d99203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d7387, d99203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d7388 q = 2) : d99204 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d7388, d99204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d7388, d99204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d7418 q = 2) : d99210 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7418, d99210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7418, d99210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7851 q selected
  have h18 (q : Pattern) (selected : d463 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro718 q selected
  have h19 (q : Pattern) (selected : d7419 q = 2) : d99211 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7419, d99211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d7419, d99211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d7420 q = 2) : d99212 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7420, d99212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d7420, d99212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d7421 q = 2) : d99213 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d7421, d99213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d7421, d99213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d7422 q = 2) : d99214 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d7422, d99214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d7422, d99214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d7423 q = 2) : d99215 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d7423, d99215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d7423, d99215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro7853 (p : Pattern) (selected : d7429 p = 2) : d99221 p = 1 := by
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
  have h5 (q : Pattern) (selected : d7293 q = 2) : d53648 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d7293, d53648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7293, d53648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7827 q selected
  have h6 (q : Pattern) (selected : d7294 q = 2) : d53649 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d7294, d53649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7294, d53649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7295 q = 2) : d53650 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d7295, d53650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7295, d53650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7296 q = 2) : d53651 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d7296, d53651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7296, d53651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d7297 q = 2) : d53652 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d7297, d53652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7297, d53652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d7424 q = 2) : d99216 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d7424, d99216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7424, d99216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7852 q selected
  have h11 (q : Pattern) (selected : d7425 q = 2) : d99217 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d7425, d99217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7425, d99217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d7426 q = 2) : d99218 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d7426, d99218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7426, d99218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d7427 q = 2) : d99219 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d7427, d99219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7427, d99219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d7428 q = 2) : d99220 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d7428, d99220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7428, d99220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d7429 q = 2) : d99221 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d7429, d99221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d7429, d99221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro7854 (p : Pattern) (selected : d7433 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7327 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7832 q selected
    | true =>
      simp only [d7327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7328 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d482 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro722 q selected
    | true =>
      simp only [d482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d483 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7430 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7431 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7432 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7433 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7855 (p : Pattern) (selected : d7439 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7434 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7854 q selected
    | true =>
      simp only [d7434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro724 q selected
  have h2 (q : Pattern) (selected : d7435 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7436 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7437 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7438 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7439 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7856 (p : Pattern) (selected : d7442 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7327 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7832 q selected
    | true =>
      simp only [d7327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7328 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d482 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro722 q selected
    | true =>
      simp only [d482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d483 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7430 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7431 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7432 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7442 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7857 (p : Pattern) (selected : d7448 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7434 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7854 q selected
    | true =>
      simp only [d7434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro724 q selected
  have h2 (q : Pattern) (selected : d7435 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7436 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7437 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7438 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7443 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7856 q selected
    | true =>
      simp only [d7443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro727 q selected
  have h7 (q : Pattern) (selected : d7444 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7445 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d7446 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d7447 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d7448 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro7858 (p : Pattern) (selected : d7453 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7327 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7832 q selected
    | true =>
      simp only [d7327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7328 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d482 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro722 q selected
    | true =>
      simp only [d482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d483 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7430 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7431 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7452 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7453 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7859 (p : Pattern) (selected : d7460 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7327 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7832 q selected
    | true =>
      simp only [d7327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7328 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d482 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro722 q selected
    | true =>
      simp only [d482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d483 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7430 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7458 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7459 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7460 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7860 (p : Pattern) (selected : d7465 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d549 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro736 q selected
    | true =>
      simp only [d549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro694 q selected
  have h2 (q : Pattern) (selected : d550 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d551 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d325 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro694 q selected
    | true =>
      simp only [d325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro664 q selected
  have h5 (q : Pattern) (selected : d326 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d327 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d552 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7464 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d7465 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro7861 (p : Pattern) (selected : d7471 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7466 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7860 q selected
    | true =>
      simp only [d7466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7467 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7327 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7832 q selected
    | true =>
      simp only [d7327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7328 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7468 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7469 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7470 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7471 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7862 (p : Pattern) (selected : d7474 p = 2) : d7326 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d580 q = 2) : d325 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d580, d325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro741 q selected
    | true =>
      simp only [d580, d325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro699 q selected
  have h2 (q : Pattern) (selected : d581 q = 2) : d326 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d581, d326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d581, d326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d582 q = 2) : d327 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d582, d327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d582, d327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d356 q = 2) : d145 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d356, d145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro699 q selected
    | true =>
      simp only [d356, d145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro669 q selected
  have h5 (q : Pattern) (selected : d357 q = 2) : d146 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d357, d146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d357, d146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d358 q = 2) : d147 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d358, d147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d358, d147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d583 q = 2) : d328 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d583, d328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d583, d328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7473 q = 2) : d7325 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7473, d7325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7473, d7325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d7474 q = 2) : d7326 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7474, d7326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7474, d7326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro7863 (p : Pattern) (selected : d7480 p = 2) : d7433 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7475 q = 2) : d7327 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7475, d7327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7862 q selected
    | true =>
      simp only [d7475, d7327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7476 q = 2) : d7328 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7476, d7328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7476, d7328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d591 q = 2) : d482 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d591, d482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro743 q selected
    | true =>
      simp only [d591, d482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d592 q = 2) : d483 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d592, d483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d592, d483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7477 q = 2) : d7430 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7477, d7430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7477, d7430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7478 q = 2) : d7431 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7478, d7431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7478, d7431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7479 q = 2) : d7432 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7479, d7432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7479, d7432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7480 q = 2) : d7433 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7480, d7433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7480, d7433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7864 (p : Pattern) (selected : d7486 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7327 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7832 q selected
    | true =>
      simp only [d7327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7328 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7483 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7484 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d7485 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d7486 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7865 (p : Pattern) (selected : d7492 p = 2) : d7439 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7454 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7858 q selected
    | true =>
      simp only [d7454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro730 q selected
  have h2 (q : Pattern) (selected : d7455 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7456 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7457 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7461 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7859 q selected
    | true =>
      simp only [d7461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro732 q selected
  have h6 (q : Pattern) (selected : d7462 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7463 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7472 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7861 q selected
    | true =>
      simp only [d7472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7854 q selected
  have h9 (q : Pattern) (selected : d7481 q = 2) : d7434 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7481, d7434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7863 q selected
    | true =>
      simp only [d7481, d7434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro745 q selected
  have h10 (q : Pattern) (selected : d7482 q = 2) : d7435 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7482, d7435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7482, d7435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d7487 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7864 q selected
    | true =>
      simp only [d7487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d7488 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d7488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d7489 q = 2) : d7436 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7489, d7436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d7489, d7436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d7490 q = 2) : d7437 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7490, d7437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7490, d7437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d7491 q = 2) : d7438 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7491, d7438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7491, d7438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d7492 q = 2) : d7439 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7492, d7439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7492, d7439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro7866 (p : Pattern) (selected : d7493 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7327 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7832 q selected
    | true =>
      simp only [d7327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7328 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d482 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro722 q selected
    | true =>
      simp only [d482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d483 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7430 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7431 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7452 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7493 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7867 (p : Pattern) (selected : d7498 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7327 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7832 q selected
    | true =>
      simp only [d7327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7328 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d482 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro722 q selected
    | true =>
      simp only [d482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d483 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7430 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7458 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7459 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7498 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7868 (p : Pattern) (selected : d7502 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7466 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7860 q selected
    | true =>
      simp only [d7466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7467 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7327 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7832 q selected
    | true =>
      simp only [d7327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7328 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7468 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7469 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7470 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7502 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7869 (p : Pattern) (selected : d7504 p = 2) : d7442 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7475 q = 2) : d7327 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7475, d7327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7862 q selected
    | true =>
      simp only [d7475, d7327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7476 q = 2) : d7328 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7476, d7328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7476, d7328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d591 q = 2) : d482 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d591, d482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro743 q selected
    | true =>
      simp only [d591, d482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d592 q = 2) : d483 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d592, d483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d592, d483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7477 q = 2) : d7430 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7477, d7430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7477, d7430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7478 q = 2) : d7431 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7478, d7431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7478, d7431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7479 q = 2) : d7432 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7479, d7432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7479, d7432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7504 q = 2) : d7442 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7504, d7442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7504, d7442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7870 (p : Pattern) (selected : d7507 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7327 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7832 q selected
    | true =>
      simp only [d7327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7328 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7483 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7484 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d7485 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d7507 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7871 (p : Pattern) (selected : d7513 p = 2) : d7448 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7454 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7858 q selected
    | true =>
      simp only [d7454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro730 q selected
  have h2 (q : Pattern) (selected : d7455 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7456 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7457 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7461 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7859 q selected
    | true =>
      simp only [d7461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro732 q selected
  have h6 (q : Pattern) (selected : d7462 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7463 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7472 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7861 q selected
    | true =>
      simp only [d7472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7854 q selected
  have h9 (q : Pattern) (selected : d7481 q = 2) : d7434 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7481, d7434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7863 q selected
    | true =>
      simp only [d7481, d7434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro745 q selected
  have h10 (q : Pattern) (selected : d7482 q = 2) : d7435 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7482, d7435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7482, d7435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d7487 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7864 q selected
    | true =>
      simp only [d7487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d7488 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d7488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d7489 q = 2) : d7436 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7489, d7436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d7489, d7436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d7490 q = 2) : d7437 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7490, d7437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7490, d7437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d7491 q = 2) : d7438 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7491, d7438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7491, d7438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d7494 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7866 q selected
    | true =>
      simp only [d7494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro748 q selected
  have h17 (q : Pattern) (selected : d7495 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d7496 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d7496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d7497 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d7499 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7867 q selected
    | true =>
      simp only [d7499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro750 q selected
  have h21 (q : Pattern) (selected : d7500 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d7501 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d7501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d7503 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7868 q selected
    | true =>
      simp only [d7503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7856 q selected
  have h24 (q : Pattern) (selected : d7505 q = 2) : d7443 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7505, d7443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7869 q selected
    | true =>
      simp only [d7505, d7443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro753 q selected
  have h25 (q : Pattern) (selected : d7506 q = 2) : d7444 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7506, d7444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d7506, d7444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d7508 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7870 q selected
    | true =>
      simp only [d7508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d7509 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d7509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d7510 q = 2) : d7445 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7510, d7445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d7510, d7445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d7511 q = 2) : d7446 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7511, d7446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d7511, d7446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d7512 q = 2) : d7447 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7512, d7447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d7512, d7447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d7513 q = 2) : d7448 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7513, d7448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d7513, d7448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro7872 (p : Pattern) (selected : d7515 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7434 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7854 q selected
    | true =>
      simp only [d7434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro724 q selected
  have h2 (q : Pattern) (selected : d7435 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7436 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7437 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7438 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d633 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro724 q selected
    | true =>
      simp only [d633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d634 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d635 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d636 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d637 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d7515 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro7873 (p : Pattern) (selected : d7522 p = 2) : d99224 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7503 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7868 q selected
    | true =>
      simp only [d7503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7856 q selected
  have h2 (q : Pattern) (selected : d7505 q = 2) : d7443 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7505, d7443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7869 q selected
    | true =>
      simp only [d7505, d7443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro753 q selected
  have h3 (q : Pattern) (selected : d7506 q = 2) : d7444 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7506, d7444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d7506, d7444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d7508 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7870 q selected
    | true =>
      simp only [d7508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d7509 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d7510 q = 2) : d7445 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7510, d7445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7510, d7445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7520 q = 2) : d7446 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7520, d7446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7520, d7446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7521 q = 2) : d7447 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7521, d7447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7521, d7447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d7522 q = 2) : d99224 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7522, d99224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7522, d99224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro7874 (p : Pattern) (selected : d7529 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d665 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro759 q selected
    | true =>
      simp only [d665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro711 q selected
  have h2 (q : Pattern) (selected : d666 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d667 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d418 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro711 q selected
    | true =>
      simp only [d418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro680 q selected
  have h5 (q : Pattern) (selected : d419 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d420 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d668 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7528 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d7529 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro7875 (p : Pattern) (selected : d7535 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7530 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7874 q selected
    | true =>
      simp only [d7530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7531 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7391 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7846 q selected
    | true =>
      simp only [d7391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7392 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7532 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7533 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7534 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7535 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7876 (p : Pattern) (selected : d7539 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7391 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7846 q selected
    | true =>
      simp only [d7391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7392 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d684 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro763 q selected
    | true =>
      simp only [d684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d685 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7536 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7537 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7538 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7539 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7877 (p : Pattern) (selected : d7542 p = 2) : d7390 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d697 q = 2) : d418 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d697, d418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro765 q selected
    | true =>
      simp only [d697, d418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro714 q selected
  have h2 (q : Pattern) (selected : d698 q = 2) : d419 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d698, d419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d698, d419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d699 q = 2) : d420 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d699, d420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d699, d420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d437 q = 2) : d232 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d437, d232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro714 q selected
    | true =>
      simp only [d437, d232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro683 q selected
  have h5 (q : Pattern) (selected : d438 q = 2) : d233 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d438, d233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d438, d233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d439 q = 2) : d234 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d439, d234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d439, d234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d700 q = 2) : d421 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d700, d421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d700, d421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7541 q = 2) : d7389 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7541, d7389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7541, d7389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d7542 q = 2) : d7390 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7542, d7390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7542, d7390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro7878 (p : Pattern) (selected : d7548 p = 2) : d7539 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7543 q = 2) : d7391 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7543, d7391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7877 q selected
    | true =>
      simp only [d7543, d7391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7544 q = 2) : d7392 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7544, d7392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7544, d7392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d708 q = 2) : d684 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d708, d684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro767 q selected
    | true =>
      simp only [d708, d684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d709 q = 2) : d685 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d709, d685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d709, d685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7545 q = 2) : d7536 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7545, d7536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7545, d7536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7546 q = 2) : d7537 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7546, d7537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7546, d7537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7547 q = 2) : d7538 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7547, d7538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7547, d7538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7548 q = 2) : d7539 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7548, d7539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7548, d7539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7879 (p : Pattern) (selected : d7554 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7391 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7846 q selected
    | true =>
      simp only [d7391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7392 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7551 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7552 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d7553 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d7554 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7880 (p : Pattern) (selected : d7560 p = 2) : d99235 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7540 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7875 q selected
    | true =>
      simp only [d7540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7876 q selected
  have h2 (q : Pattern) (selected : d7549 q = 2) : d99230 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7549, d99230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7878 q selected
    | true =>
      simp only [d7549, d99230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro769 q selected
  have h3 (q : Pattern) (selected : d7550 q = 2) : d99231 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7550, d99231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d7550, d99231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d7555 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7879 q selected
    | true =>
      simp only [d7555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d7556 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d7557 q = 2) : d99232 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7557, d99232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7557, d99232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7558 q = 2) : d99233 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7558, d99233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7558, d99233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7559 q = 2) : d99234 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7559, d99234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7559, d99234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d7560 q = 2) : d99235 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7560, d99235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7560, d99235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro7881 (p : Pattern) (selected : d7566 p = 2) : d99241 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7440 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7855 q selected
  have h2 (q : Pattern) (selected : d7441 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d7441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d7449 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7855 q selected
    | true =>
      simp only [d7449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7857 q selected
  have h4 (q : Pattern) (selected : d7450 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d7451 q = 2) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7514 q = 2) : d7449 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7514, d7449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7865 q selected
    | true =>
      simp only [d7514, d7449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7871 q selected
  have h7 (q : Pattern) (selected : d7516 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7872 q selected
    | true =>
      simp only [d7516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro756 q selected
  have h8 (q : Pattern) (selected : d7517 q = 2) : d7450 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7517, d7450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7517, d7450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d7518 q = 2) : d99222 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7518, d99222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7518, d99222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d7519 q = 2) : d99223 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d7519, d99223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7519, d99223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d7523 q = 2) : d99225 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7523, d99225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7523, d99225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7873 q selected
  have h12 (q : Pattern) (selected : d654 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro758 q selected
  have h13 (q : Pattern) (selected : d7524 q = 2) : d99226 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7524, d99226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d7524, d99226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d7525 q = 2) : d99227 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7525, d99227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d7525, d99227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d7526 q = 2) : d99228 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d7526, d99228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d7526, d99228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d7527 q = 2) : d99229 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d7527, d99229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d7527, d99229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d7561 q = 2) : d99236 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7561, d99236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7561, d99236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7880 q selected
  have h18 (q : Pattern) (selected : d737 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro772 q selected
  have h19 (q : Pattern) (selected : d7562 q = 2) : d99237 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7562, d99237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d7562, d99237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d7563 q = 2) : d99238 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7563, d99238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d7563, d99238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d7564 q = 2) : d99239 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d7564, d99239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d7564, d99239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d7565 q = 2) : d99240 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d7565, d99240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d7565, d99240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d7566 q = 2) : d99241 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d7566, d99241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d7566, d99241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro7882 (p : Pattern) (selected : d7572 p = 2) : d99247 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7567 q = 2) : d99242 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d7567, d99242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7567, d99242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7881 q selected
  have h2 (q : Pattern) (selected : d7568 q = 2) : d99243 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d7568, d99243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7568, d99243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7569 q = 2) : d99244 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d7569, d99244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7569, d99244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d7570 q = 2) : d99245 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d7570, d99245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7570, d99245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7571 q = 2) : d99246 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d7571, d99246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7571, d99246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7572 q = 2) : d99247 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d7572, d99247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7572, d99247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7883 (p : Pattern) (selected : d7575 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d759 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro776 q selected
    | true =>
      simp only [d759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro777 q selected
  have h2 (q : Pattern) (selected : d760 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d761 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d763 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro777 q selected
    | true =>
      simp only [d763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro778 q selected
  have h5 (q : Pattern) (selected : d764 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d765 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d766 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7574 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d7575 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro7884 (p : Pattern) (selected : d7581 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7576 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7883 q selected
    | true =>
      simp only [d7576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7577 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d774 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro780 q selected
    | true =>
      simp only [d774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d775 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7578 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7579 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7580 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7581 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7885 (p : Pattern) (selected : d7587 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7582 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7884 q selected
    | true =>
      simp only [d7582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro782 q selected
  have h2 (q : Pattern) (selected : d7583 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7584 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7585 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7586 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7587 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7886 (p : Pattern) (selected : d7590 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7576 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7883 q selected
    | true =>
      simp only [d7576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7577 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d774 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro780 q selected
    | true =>
      simp only [d774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d775 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7578 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7579 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7580 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7590 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7887 (p : Pattern) (selected : d7596 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7582 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7884 q selected
    | true =>
      simp only [d7582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro782 q selected
  have h2 (q : Pattern) (selected : d7583 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7584 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7585 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7586 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7591 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7886 q selected
    | true =>
      simp only [d7591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro785 q selected
  have h7 (q : Pattern) (selected : d7592 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7593 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d7594 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d7595 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d7596 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro7888 (p : Pattern) (selected : d7601 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7576 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7883 q selected
    | true =>
      simp only [d7576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7577 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d774 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro780 q selected
    | true =>
      simp only [d774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d775 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7578 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7579 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7600 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7601 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7889 (p : Pattern) (selected : d7608 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7576 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7883 q selected
    | true =>
      simp only [d7576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7577 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d774 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro780 q selected
    | true =>
      simp only [d774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d775 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7578 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7606 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7607 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7608 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7890 (p : Pattern) (selected : d7613 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d840 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro794 q selected
    | true =>
      simp only [d840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro776 q selected
  have h2 (q : Pattern) (selected : d841 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d842 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d759 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro776 q selected
    | true =>
      simp only [d759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro777 q selected
  have h5 (q : Pattern) (selected : d760 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d761 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d843 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7612 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d7613 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro7891 (p : Pattern) (selected : d7619 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7614 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7890 q selected
    | true =>
      simp only [d7614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7615 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7576 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7883 q selected
    | true =>
      simp only [d7576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7577 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7616 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7617 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7618 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7619 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7892 (p : Pattern) (selected : d7622 p = 2) : d7575 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d882 q = 2) : d759 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d882, d759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro801 q selected
    | true =>
      simp only [d882, d759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro802 q selected
  have h2 (q : Pattern) (selected : d883 q = 2) : d760 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d883, d760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d883, d760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d884 q = 2) : d761 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d884, d761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d884, d761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d886 q = 2) : d763 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d886, d763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro802 q selected
    | true =>
      simp only [d886, d763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro803 q selected
  have h5 (q : Pattern) (selected : d887 q = 2) : d764 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d887, d764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d887, d764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d888 q = 2) : d765 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d888, d765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d888, d765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d889 q = 2) : d766 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d889, d766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d889, d766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7621 q = 2) : d7574 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7621, d7574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7621, d7574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d7622 q = 2) : d7575 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7622, d7575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7622, d7575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro7893 (p : Pattern) (selected : d7628 p = 2) : d7581 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7623 q = 2) : d7576 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7623, d7576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7892 q selected
    | true =>
      simp only [d7623, d7576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7624 q = 2) : d7577 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7624, d7577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7624, d7577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d897 q = 2) : d774 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d897, d774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro805 q selected
    | true =>
      simp only [d897, d774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d898 q = 2) : d775 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d898, d775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d898, d775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7625 q = 2) : d7578 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7625, d7578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7625, d7578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7626 q = 2) : d7579 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7626, d7579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7626, d7579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7627 q = 2) : d7580 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7627, d7580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7627, d7580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7628 q = 2) : d7581 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7628, d7581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7628, d7581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7894 (p : Pattern) (selected : d7634 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7576 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7883 q selected
    | true =>
      simp only [d7576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7577 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7631 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7632 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d7633 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d7634 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7895 (p : Pattern) (selected : d7640 p = 2) : d7587 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7602 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7888 q selected
    | true =>
      simp only [d7602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro788 q selected
  have h2 (q : Pattern) (selected : d7603 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7604 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7605 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7609 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7889 q selected
    | true =>
      simp only [d7609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro790 q selected
  have h6 (q : Pattern) (selected : d7610 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7611 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7620 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7891 q selected
    | true =>
      simp only [d7620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7884 q selected
  have h9 (q : Pattern) (selected : d7629 q = 2) : d7582 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7629, d7582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7893 q selected
    | true =>
      simp only [d7629, d7582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro807 q selected
  have h10 (q : Pattern) (selected : d7630 q = 2) : d7583 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7630, d7583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7630, d7583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d7635 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7894 q selected
    | true =>
      simp only [d7635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d7636 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d7636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d7637 q = 2) : d7584 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7637, d7584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d7637, d7584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d7638 q = 2) : d7585 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7638, d7585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7638, d7585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d7639 q = 2) : d7586 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7639, d7586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7639, d7586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d7640 q = 2) : d7587 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7640, d7587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7640, d7587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro7896 (p : Pattern) (selected : d7641 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7576 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7883 q selected
    | true =>
      simp only [d7576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7577 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d774 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro780 q selected
    | true =>
      simp only [d774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d775 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7578 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7579 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7600 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7641 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7897 (p : Pattern) (selected : d7646 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7576 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7883 q selected
    | true =>
      simp only [d7576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7577 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d774 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro780 q selected
    | true =>
      simp only [d774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d775 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7578 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7606 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7607 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7646 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7898 (p : Pattern) (selected : d7650 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7614 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7890 q selected
    | true =>
      simp only [d7614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7615 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7576 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7883 q selected
    | true =>
      simp only [d7576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7577 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7616 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7617 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7618 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7650 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7899 (p : Pattern) (selected : d7652 p = 2) : d7590 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7623 q = 2) : d7576 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7623, d7576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7892 q selected
    | true =>
      simp only [d7623, d7576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7624 q = 2) : d7577 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7624, d7577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7624, d7577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d897 q = 2) : d774 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d897, d774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro805 q selected
    | true =>
      simp only [d897, d774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d898 q = 2) : d775 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d898, d775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d898, d775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7625 q = 2) : d7578 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7625, d7578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7625, d7578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7626 q = 2) : d7579 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7626, d7579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7626, d7579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7627 q = 2) : d7580 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7627, d7580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7627, d7580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7652 q = 2) : d7590 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7652, d7590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7652, d7590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7900 (p : Pattern) (selected : d7655 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7576 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7883 q selected
    | true =>
      simp only [d7576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7577 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7631 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7632 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d7633 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d7655 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7901 (p : Pattern) (selected : d7661 p = 2) : d7596 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7602 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7888 q selected
    | true =>
      simp only [d7602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro788 q selected
  have h2 (q : Pattern) (selected : d7603 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7604 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7605 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7609 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7889 q selected
    | true =>
      simp only [d7609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro790 q selected
  have h6 (q : Pattern) (selected : d7610 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7611 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7620 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7891 q selected
    | true =>
      simp only [d7620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7884 q selected
  have h9 (q : Pattern) (selected : d7629 q = 2) : d7582 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7629, d7582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7893 q selected
    | true =>
      simp only [d7629, d7582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro807 q selected
  have h10 (q : Pattern) (selected : d7630 q = 2) : d7583 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7630, d7583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7630, d7583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d7635 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7894 q selected
    | true =>
      simp only [d7635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d7636 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d7636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d7637 q = 2) : d7584 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7637, d7584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d7637, d7584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d7638 q = 2) : d7585 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7638, d7585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7638, d7585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d7639 q = 2) : d7586 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7639, d7586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7639, d7586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d7642 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7896 q selected
    | true =>
      simp only [d7642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro810 q selected
  have h17 (q : Pattern) (selected : d7643 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d7644 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d7644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d7645 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d7647 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7897 q selected
    | true =>
      simp only [d7647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro812 q selected
  have h21 (q : Pattern) (selected : d7648 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d7649 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d7649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d7651 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7898 q selected
    | true =>
      simp only [d7651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7886 q selected
  have h24 (q : Pattern) (selected : d7653 q = 2) : d7591 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7653, d7591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7899 q selected
    | true =>
      simp only [d7653, d7591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro815 q selected
  have h25 (q : Pattern) (selected : d7654 q = 2) : d7592 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7654, d7592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d7654, d7592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d7656 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7900 q selected
    | true =>
      simp only [d7656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d7657 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d7657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d7658 q = 2) : d7593 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7658, d7593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d7658, d7593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d7659 q = 2) : d7594 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7659, d7594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d7659, d7594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d7660 q = 2) : d7595 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7660, d7595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d7660, d7595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d7661 q = 2) : d7596 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7661, d7596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d7661, d7596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro7902 (p : Pattern) (selected : d7663 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7582 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7884 q selected
    | true =>
      simp only [d7582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro782 q selected
  have h2 (q : Pattern) (selected : d7583 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7584 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7585 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7586 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
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
  have h11 (q : Pattern) (selected : d7663 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro7903 (p : Pattern) (selected : d7670 p = 2) : d99251 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7651 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7898 q selected
    | true =>
      simp only [d7651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7886 q selected
  have h2 (q : Pattern) (selected : d7653 q = 2) : d7591 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7653, d7591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7899 q selected
    | true =>
      simp only [d7653, d7591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro815 q selected
  have h3 (q : Pattern) (selected : d7654 q = 2) : d7592 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7654, d7592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d7654, d7592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d7656 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7900 q selected
    | true =>
      simp only [d7656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d7657 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d7658 q = 2) : d7593 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7658, d7593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7658, d7593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7668 q = 2) : d7594 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7668, d7594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7668, d7594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7669 q = 2) : d7595 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7669, d7595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7669, d7595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d7670 q = 2) : d99251 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7670, d99251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7670, d99251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro7904 (p : Pattern) (selected : d7677 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d977 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro821 q selected
    | true =>
      simp only [d977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro822 q selected
  have h2 (q : Pattern) (selected : d978 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d979 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d982 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro822 q selected
    | true =>
      simp only [d982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro823 q selected
  have h5 (q : Pattern) (selected : d983 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d984 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d985 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7676 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d7677 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro7905 (p : Pattern) (selected : d7681 p = 2) : d0 p = 1 := by
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
  have h8 (q : Pattern) (selected : d7680 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d7681 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro7906 (p : Pattern) (selected : d7687 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7678 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7904 q selected
    | true =>
      simp only [d7678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7679 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7682 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7905 q selected
    | true =>
      simp only [d7682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7683 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7684 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7685 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7686 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7687 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7907 (p : Pattern) (selected : d7691 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7682 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7905 q selected
    | true =>
      simp only [d7682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7683 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1006 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro828 q selected
    | true =>
      simp only [d1006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1007 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7688 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7689 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7690 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7691 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7908 (p : Pattern) (selected : d7694 p = 2) : d7681 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1026 q = 2) : d982 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1026, d982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro830 q selected
    | true =>
      simp only [d1026, d982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro831 q selected
  have h2 (q : Pattern) (selected : d1027 q = 2) : d983 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1027, d983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1027, d983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1028 q = 2) : d984 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1028, d984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1028, d984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1030 q = 2) : d987 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1030, d987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro831 q selected
    | true =>
      simp only [d1030, d987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro832 q selected
  have h5 (q : Pattern) (selected : d1031 q = 2) : d988 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1031, d988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1031, d988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1032 q = 2) : d989 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1032, d989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1032, d989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d1033 q = 2) : d990 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1033, d990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1033, d990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7693 q = 2) : d7680 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7693, d7680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7693, d7680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d7694 q = 2) : d7681 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7694, d7681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7694, d7681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro7909 (p : Pattern) (selected : d7700 p = 2) : d7691 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7695 q = 2) : d7682 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7695, d7682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7908 q selected
    | true =>
      simp only [d7695, d7682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7696 q = 2) : d7683 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7696, d7683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7696, d7683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1041 q = 2) : d1006 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1041, d1006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro834 q selected
    | true =>
      simp only [d1041, d1006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1042 q = 2) : d1007 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1042, d1007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1042, d1007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7697 q = 2) : d7688 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7697, d7688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7697, d7688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7698 q = 2) : d7689 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7698, d7689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7698, d7689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7699 q = 2) : d7690 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7699, d7690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7699, d7690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7700 q = 2) : d7691 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7700, d7691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7700, d7691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7910 (p : Pattern) (selected : d7706 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7682 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7905 q selected
    | true =>
      simp only [d7682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7683 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7703 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7704 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d7705 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d7706 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7911 (p : Pattern) (selected : d7712 p = 2) : d99262 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7692 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7906 q selected
    | true =>
      simp only [d7692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7907 q selected
  have h2 (q : Pattern) (selected : d7701 q = 2) : d99257 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7701, d99257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7909 q selected
    | true =>
      simp only [d7701, d99257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro836 q selected
  have h3 (q : Pattern) (selected : d7702 q = 2) : d99258 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7702, d99258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d7702, d99258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d7707 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7910 q selected
    | true =>
      simp only [d7707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d7708 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d7709 q = 2) : d99259 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7709, d99259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7709, d99259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7710 q = 2) : d99260 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7710, d99260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7710, d99260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7711 q = 2) : d99261 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7711, d99261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7711, d99261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d7712 q = 2) : d99262 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7712, d99262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7712, d99262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro7912 (p : Pattern) (selected : d7718 p = 2) : d99268 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7588 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7885 q selected
  have h2 (q : Pattern) (selected : d7589 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d7589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d7597 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7885 q selected
    | true =>
      simp only [d7597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7887 q selected
  have h4 (q : Pattern) (selected : d7598 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d7599 q = 2) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7662 q = 2) : d7597 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7662, d7597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7895 q selected
    | true =>
      simp only [d7662, d7597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7901 q selected
  have h7 (q : Pattern) (selected : d7664 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7902 q selected
    | true =>
      simp only [d7664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro818 q selected
  have h8 (q : Pattern) (selected : d7665 q = 2) : d7598 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7665, d7598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7665, d7598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d7666 q = 2) : d99249 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7666, d99249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7666, d99249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d7667 q = 2) : d99250 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d7667, d99250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7667, d99250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d7671 q = 2) : d99252 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7671, d99252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7671, d99252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7903 q selected
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
  have h13 (q : Pattern) (selected : d7672 q = 2) : d99253 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7672, d99253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d7672, d99253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d7673 q = 2) : d99254 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7673, d99254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d7673, d99254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d7674 q = 2) : d99255 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d7674, d99255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d7674, d99255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d7675 q = 2) : d99256 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d7675, d99256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d7675, d99256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d7713 q = 2) : d99263 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7713, d99263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7713, d99263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7911 q selected
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
  have h19 (q : Pattern) (selected : d7714 q = 2) : d99264 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7714, d99264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d7714, d99264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d7715 q = 2) : d99265 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7715, d99265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d7715, d99265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d7716 q = 2) : d99266 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d7716, d99266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d7716, d99266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d7717 q = 2) : d99267 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d7717, d99267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d7717, d99267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d7718 q = 2) : d99268 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d7718, d99268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d7718, d99268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro7913 (p : Pattern) (selected : d7724 p = 2) : d99274 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7719 q = 2) : d99269 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d7719, d99269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7719, d99269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7912 q selected
  have h2 (q : Pattern) (selected : d7720 q = 2) : d99270 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d7720, d99270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7720, d99270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7721 q = 2) : d99271 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d7721, d99271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7721, d99271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d7722 q = 2) : d99272 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d7722, d99272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7722, d99272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7723 q = 2) : d99273 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d7723, d99273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7723, d99273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7724 q = 2) : d99274 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d7724, d99274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7724, d99274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7914 (p : Pattern) (selected : d7728 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1129 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro847 q selected
    | true =>
      simp only [d1129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro848 q selected
  have h2 (q : Pattern) (selected : d1130 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1131 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1142 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro848 q selected
    | true =>
      simp only [d1142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro850 q selected
  have h5 (q : Pattern) (selected : d1143 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1144 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d1145 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7727 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d7728 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro7915 (p : Pattern) (selected : d7734 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7729 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7914 q selected
    | true =>
      simp only [d7729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7730 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1153 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro852 q selected
    | true =>
      simp only [d1153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1154 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7731 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7732 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7733 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7734 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7916 (p : Pattern) (selected : d7740 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7735 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7915 q selected
    | true =>
      simp only [d7735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro854 q selected
  have h2 (q : Pattern) (selected : d7736 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7737 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7738 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7739 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7740 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7917 (p : Pattern) (selected : d7743 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7729 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7914 q selected
    | true =>
      simp only [d7729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7730 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1153 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro852 q selected
    | true =>
      simp only [d1153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1154 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7731 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7732 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7733 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7743 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7918 (p : Pattern) (selected : d7749 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7735 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7915 q selected
    | true =>
      simp only [d7735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro854 q selected
  have h2 (q : Pattern) (selected : d7736 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7737 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7738 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7739 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7744 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7917 q selected
    | true =>
      simp only [d7744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro857 q selected
  have h7 (q : Pattern) (selected : d7745 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7746 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d7747 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d7748 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d7749 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro7919 (p : Pattern) (selected : d7754 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7729 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7914 q selected
    | true =>
      simp only [d7729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7730 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1153 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro852 q selected
    | true =>
      simp only [d1153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1154 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7731 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7732 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7753 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7754 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7920 (p : Pattern) (selected : d7761 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7729 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7914 q selected
    | true =>
      simp only [d7729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7730 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1153 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro852 q selected
    | true =>
      simp only [d1153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1154 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7731 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7759 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7760 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7761 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7921 (p : Pattern) (selected : d7766 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1216 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro866 q selected
    | true =>
      simp only [d1216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro847 q selected
  have h2 (q : Pattern) (selected : d1217 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1218 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1129 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro847 q selected
    | true =>
      simp only [d1129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro848 q selected
  have h5 (q : Pattern) (selected : d1130 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1131 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d1219 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7765 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d7766 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro7922 (p : Pattern) (selected : d7772 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7767 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7921 q selected
    | true =>
      simp only [d7767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7768 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7729 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7914 q selected
    | true =>
      simp only [d7729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7730 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7769 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7770 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7771 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7772 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7923 (p : Pattern) (selected : d7775 p = 2) : d7728 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1284 q = 2) : d1129 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1284, d1129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro876 q selected
    | true =>
      simp only [d1284, d1129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro877 q selected
  have h2 (q : Pattern) (selected : d1285 q = 2) : d1130 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1285, d1130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1285, d1130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1286 q = 2) : d1131 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1286, d1131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1286, d1131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1297 q = 2) : d1142 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1297, d1142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro877 q selected
    | true =>
      simp only [d1297, d1142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro879 q selected
  have h5 (q : Pattern) (selected : d1298 q = 2) : d1143 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1298, d1143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1298, d1143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1299 q = 2) : d1144 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1299, d1144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1299, d1144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d1300 q = 2) : d1145 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1300, d1145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1300, d1145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7774 q = 2) : d7727 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7774, d7727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7774, d7727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d7775 q = 2) : d7728 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7775, d7728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7775, d7728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro7924 (p : Pattern) (selected : d7781 p = 2) : d7734 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7776 q = 2) : d7729 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7776, d7729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7923 q selected
    | true =>
      simp only [d7776, d7729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7777 q = 2) : d7730 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7777, d7730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7777, d7730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1308 q = 2) : d1153 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1308, d1153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro881 q selected
    | true =>
      simp only [d1308, d1153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1309 q = 2) : d1154 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1309, d1154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1309, d1154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7778 q = 2) : d7731 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7778, d7731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7778, d7731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7779 q = 2) : d7732 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7779, d7732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7779, d7732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7780 q = 2) : d7733 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7780, d7733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7780, d7733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7781 q = 2) : d7734 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7781, d7734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7781, d7734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7925 (p : Pattern) (selected : d7787 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7729 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7914 q selected
    | true =>
      simp only [d7729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7730 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7784 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7785 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d7786 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d7787 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7926 (p : Pattern) (selected : d7793 p = 2) : d7740 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7755 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7919 q selected
    | true =>
      simp only [d7755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro860 q selected
  have h2 (q : Pattern) (selected : d7756 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7757 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7758 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7762 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7920 q selected
    | true =>
      simp only [d7762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro862 q selected
  have h6 (q : Pattern) (selected : d7763 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7764 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7773 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7922 q selected
    | true =>
      simp only [d7773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7915 q selected
  have h9 (q : Pattern) (selected : d7782 q = 2) : d7735 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7782, d7735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7924 q selected
    | true =>
      simp only [d7782, d7735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro883 q selected
  have h10 (q : Pattern) (selected : d7783 q = 2) : d7736 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7783, d7736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7783, d7736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d7788 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7925 q selected
    | true =>
      simp only [d7788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d7789 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d7789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d7790 q = 2) : d7737 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7790, d7737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d7790, d7737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d7791 q = 2) : d7738 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7791, d7738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7791, d7738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d7792 q = 2) : d7739 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7792, d7739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7792, d7739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d7793 q = 2) : d7740 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7793, d7740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7793, d7740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro7927 (p : Pattern) (selected : d7794 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7729 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7914 q selected
    | true =>
      simp only [d7729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7730 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1153 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro852 q selected
    | true =>
      simp only [d1153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1154 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7731 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7732 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7753 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7794 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7928 (p : Pattern) (selected : d7799 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7729 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7914 q selected
    | true =>
      simp only [d7729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7730 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1153 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro852 q selected
    | true =>
      simp only [d1153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1154 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7731 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7759 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7760 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7799 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7929 (p : Pattern) (selected : d7803 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7767 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7921 q selected
    | true =>
      simp only [d7767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7768 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7729 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7914 q selected
    | true =>
      simp only [d7729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7730 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7769 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7770 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7771 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7803 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7930 (p : Pattern) (selected : d7805 p = 2) : d7743 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7776 q = 2) : d7729 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7776, d7729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7923 q selected
    | true =>
      simp only [d7776, d7729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7777 q = 2) : d7730 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7777, d7730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7777, d7730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1308 q = 2) : d1153 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1308, d1153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro881 q selected
    | true =>
      simp only [d1308, d1153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1309 q = 2) : d1154 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1309, d1154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1309, d1154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7778 q = 2) : d7731 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7778, d7731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7778, d7731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7779 q = 2) : d7732 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7779, d7732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7779, d7732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7780 q = 2) : d7733 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7780, d7733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7780, d7733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7805 q = 2) : d7743 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7805, d7743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7805, d7743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7931 (p : Pattern) (selected : d7808 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7729 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7914 q selected
    | true =>
      simp only [d7729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7730 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7784 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7785 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d7786 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d7808 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7932 (p : Pattern) (selected : d7814 p = 2) : d7749 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7755 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7919 q selected
    | true =>
      simp only [d7755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro860 q selected
  have h2 (q : Pattern) (selected : d7756 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7757 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7758 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7762 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7920 q selected
    | true =>
      simp only [d7762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro862 q selected
  have h6 (q : Pattern) (selected : d7763 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7764 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7773 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7922 q selected
    | true =>
      simp only [d7773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7915 q selected
  have h9 (q : Pattern) (selected : d7782 q = 2) : d7735 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7782, d7735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7924 q selected
    | true =>
      simp only [d7782, d7735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro883 q selected
  have h10 (q : Pattern) (selected : d7783 q = 2) : d7736 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7783, d7736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7783, d7736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d7788 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7925 q selected
    | true =>
      simp only [d7788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d7789 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d7789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d7790 q = 2) : d7737 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7790, d7737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d7790, d7737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d7791 q = 2) : d7738 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7791, d7738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7791, d7738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d7792 q = 2) : d7739 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7792, d7739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7792, d7739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d7795 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7927 q selected
    | true =>
      simp only [d7795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro886 q selected
  have h17 (q : Pattern) (selected : d7796 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d7797 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d7797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d7798 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d7800 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7928 q selected
    | true =>
      simp only [d7800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro888 q selected
  have h21 (q : Pattern) (selected : d7801 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d7802 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d7802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d7804 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7929 q selected
    | true =>
      simp only [d7804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7917 q selected
  have h24 (q : Pattern) (selected : d7806 q = 2) : d7744 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7806, d7744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7930 q selected
    | true =>
      simp only [d7806, d7744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro891 q selected
  have h25 (q : Pattern) (selected : d7807 q = 2) : d7745 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7807, d7745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d7807, d7745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d7809 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7931 q selected
    | true =>
      simp only [d7809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d7810 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d7810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d7811 q = 2) : d7746 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7811, d7746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d7811, d7746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d7812 q = 2) : d7747 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7812, d7747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d7812, d7747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d7813 q = 2) : d7748 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7813, d7748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d7813, d7748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d7814 q = 2) : d7749 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7814, d7749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d7814, d7749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro7933 (p : Pattern) (selected : d7816 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7735 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7915 q selected
    | true =>
      simp only [d7735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro854 q selected
  have h2 (q : Pattern) (selected : d7736 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7737 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7738 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7739 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
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
  have h11 (q : Pattern) (selected : d7816 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro7934 (p : Pattern) (selected : d7823 p = 2) : d99279 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7804 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7929 q selected
    | true =>
      simp only [d7804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7917 q selected
  have h2 (q : Pattern) (selected : d7806 q = 2) : d7744 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7806, d7744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7930 q selected
    | true =>
      simp only [d7806, d7744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro891 q selected
  have h3 (q : Pattern) (selected : d7807 q = 2) : d7745 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7807, d7745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d7807, d7745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d7809 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7931 q selected
    | true =>
      simp only [d7809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d7810 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d7811 q = 2) : d7746 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7811, d7746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7811, d7746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7821 q = 2) : d7747 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7821, d7747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7821, d7747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7822 q = 2) : d7748 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7822, d7748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7822, d7748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d7823 q = 2) : d99279 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7823, d99279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7823, d99279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro7935 (p : Pattern) (selected : d7830 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1397 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro897 q selected
    | true =>
      simp only [d1397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro898 q selected
  have h2 (q : Pattern) (selected : d1398 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1399 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1402 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro898 q selected
    | true =>
      simp only [d1402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro899 q selected
  have h5 (q : Pattern) (selected : d1403 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1404 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d1405 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7829 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d7830 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro7936 (p : Pattern) (selected : d7834 p = 2) : d0 p = 1 := by
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
  have h8 (q : Pattern) (selected : d7833 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d7834 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro7937 (p : Pattern) (selected : d7840 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7831 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7935 q selected
    | true =>
      simp only [d7831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7832 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7835 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7936 q selected
    | true =>
      simp only [d7835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7836 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7837 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7838 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7839 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7840 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7938 (p : Pattern) (selected : d7844 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7835 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7936 q selected
    | true =>
      simp only [d7835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7836 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1431 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro904 q selected
    | true =>
      simp only [d1431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1432 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7841 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7842 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7843 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7844 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7939 (p : Pattern) (selected : d7847 p = 2) : d7834 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1455 q = 2) : d1402 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1455, d1402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro906 q selected
    | true =>
      simp only [d1455, d1402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro907 q selected
  have h2 (q : Pattern) (selected : d1456 q = 2) : d1403 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1456, d1403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1456, d1403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1457 q = 2) : d1404 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1457, d1404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1457, d1404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1464 q = 2) : d1412 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1464, d1412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro907 q selected
    | true =>
      simp only [d1464, d1412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro908 q selected
  have h5 (q : Pattern) (selected : d1465 q = 2) : d1413 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1465, d1413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1465, d1413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1466 q = 2) : d1414 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1466, d1414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1466, d1414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d1467 q = 2) : d1415 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1467, d1415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1467, d1415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7846 q = 2) : d7833 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7846, d7833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7846, d7833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d7847 q = 2) : d7834 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7847, d7834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7847, d7834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro7940 (p : Pattern) (selected : d7853 p = 2) : d7844 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7848 q = 2) : d7835 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7848, d7835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7939 q selected
    | true =>
      simp only [d7848, d7835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7849 q = 2) : d7836 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7849, d7836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7849, d7836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1475 q = 2) : d1431 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1475, d1431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro910 q selected
    | true =>
      simp only [d1475, d1431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1476 q = 2) : d1432 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1476, d1432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1476, d1432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7850 q = 2) : d7841 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7850, d7841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7850, d7841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7851 q = 2) : d7842 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7851, d7842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7851, d7842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7852 q = 2) : d7843 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7852, d7843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7852, d7843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7853 q = 2) : d7844 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7853, d7844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7853, d7844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7941 (p : Pattern) (selected : d7859 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7835 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7936 q selected
    | true =>
      simp only [d7835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7836 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7856 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7857 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d7858 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d7859 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7942 (p : Pattern) (selected : d7865 p = 2) : d99290 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7845 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7937 q selected
    | true =>
      simp only [d7845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7938 q selected
  have h2 (q : Pattern) (selected : d7854 q = 2) : d99285 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7854, d99285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7940 q selected
    | true =>
      simp only [d7854, d99285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro912 q selected
  have h3 (q : Pattern) (selected : d7855 q = 2) : d99286 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7855, d99286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d7855, d99286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d7860 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7941 q selected
    | true =>
      simp only [d7860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d7861 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d7862 q = 2) : d99287 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7862, d99287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7862, d99287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7863 q = 2) : d99288 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7863, d99288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7863, d99288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7864 q = 2) : d99289 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7864, d99289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7864, d99289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d7865 q = 2) : d99290 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7865, d99290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7865, d99290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro7943 (p : Pattern) (selected : d7871 p = 2) : d99296 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7741 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7916 q selected
  have h2 (q : Pattern) (selected : d7742 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d7742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d7750 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7916 q selected
    | true =>
      simp only [d7750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7918 q selected
  have h4 (q : Pattern) (selected : d7751 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d7752 q = 2) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7815 q = 2) : d7750 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7815, d7750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7926 q selected
    | true =>
      simp only [d7815, d7750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7932 q selected
  have h7 (q : Pattern) (selected : d7817 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7933 q selected
    | true =>
      simp only [d7817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro894 q selected
  have h8 (q : Pattern) (selected : d7818 q = 2) : d7751 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7818, d7751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7818, d7751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d7819 q = 2) : d99277 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7819, d99277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7819, d99277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d7820 q = 2) : d99278 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d7820, d99278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7820, d99278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d7824 q = 2) : d99280 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7824, d99280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7824, d99280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7934 q selected
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
  have h13 (q : Pattern) (selected : d7825 q = 2) : d99281 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7825, d99281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d7825, d99281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d7826 q = 2) : d99282 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7826, d99282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d7826, d99282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d7827 q = 2) : d99283 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d7827, d99283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d7827, d99283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d7828 q = 2) : d99284 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d7828, d99284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d7828, d99284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d7866 q = 2) : d99291 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7866, d99291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7866, d99291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7942 q selected
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
  have h19 (q : Pattern) (selected : d7867 q = 2) : d99292 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7867, d99292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d7867, d99292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d7868 q = 2) : d99293 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7868, d99293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d7868, d99293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d7869 q = 2) : d99294 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d7869, d99294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d7869, d99294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d7870 q = 2) : d99295 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d7870, d99295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d7870, d99295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d7871 q = 2) : d99296 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d7871, d99296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d7871, d99296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro7944 (p : Pattern) (selected : d7877 p = 2) : d99302 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7872 q = 2) : d99297 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d7872, d99297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7872, d99297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7943 q selected
  have h2 (q : Pattern) (selected : d7873 q = 2) : d99298 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d7873, d99298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7873, d99298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7874 q = 2) : d99299 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d7874, d99299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7874, d99299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d7875 q = 2) : d99300 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d7875, d99300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7875, d99300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7876 q = 2) : d99301 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d7876, d99301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7876, d99301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7877 q = 2) : d99302 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d7877, d99302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7877, d99302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7945 (p : Pattern) (selected : d7882 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1590 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro929 q selected
    | true =>
      simp only [d1590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro930 q selected
  have h2 (q : Pattern) (selected : d1591 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1592 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1603 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro930 q selected
    | true =>
      simp only [d1603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro932 q selected
  have h5 (q : Pattern) (selected : d1604 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1605 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d1606 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7881 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d7882 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro7946 (p : Pattern) (selected : d7888 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7883 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7945 q selected
    | true =>
      simp only [d7883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7884 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1614 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro934 q selected
    | true =>
      simp only [d1614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1615 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7885 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7886 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7887 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7888 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7947 (p : Pattern) (selected : d7894 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7889 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7946 q selected
    | true =>
      simp only [d7889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro936 q selected
  have h2 (q : Pattern) (selected : d7890 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7891 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7892 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7893 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7894 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7948 (p : Pattern) (selected : d7897 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7883 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7945 q selected
    | true =>
      simp only [d7883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7884 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1614 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro934 q selected
    | true =>
      simp only [d1614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1615 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7885 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7886 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7887 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7897 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7949 (p : Pattern) (selected : d7903 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7889 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7946 q selected
    | true =>
      simp only [d7889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro936 q selected
  have h2 (q : Pattern) (selected : d7890 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7891 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7892 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7893 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7898 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7948 q selected
    | true =>
      simp only [d7898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro939 q selected
  have h7 (q : Pattern) (selected : d7899 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7900 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d7901 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d7902 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d7903 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro7950 (p : Pattern) (selected : d7908 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7883 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7945 q selected
    | true =>
      simp only [d7883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7884 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1614 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro934 q selected
    | true =>
      simp only [d1614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1615 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7885 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7886 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7907 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7908 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7951 (p : Pattern) (selected : d7915 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7883 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7945 q selected
    | true =>
      simp only [d7883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7884 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1614 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro934 q selected
    | true =>
      simp only [d1614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1615 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7885 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7913 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7914 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7915 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7952 (p : Pattern) (selected : d7920 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1671 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro946 q selected
    | true =>
      simp only [d1671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro929 q selected
  have h2 (q : Pattern) (selected : d1672 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1673 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1590 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro929 q selected
    | true =>
      simp only [d1590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro930 q selected
  have h5 (q : Pattern) (selected : d1591 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1592 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d1674 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7919 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d7920 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro7953 (p : Pattern) (selected : d7926 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7921 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7952 q selected
    | true =>
      simp only [d7921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7922 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7883 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7945 q selected
    | true =>
      simp only [d7883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7884 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7923 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7924 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7925 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7926 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7954 (p : Pattern) (selected : d7929 p = 2) : d7882 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1761 q = 2) : d1590 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1761, d1590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro962 q selected
    | true =>
      simp only [d1761, d1590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro963 q selected
  have h2 (q : Pattern) (selected : d1762 q = 2) : d1591 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1762, d1591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1762, d1591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1763 q = 2) : d1592 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1763, d1592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1763, d1592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1774 q = 2) : d1603 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1774, d1603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro963 q selected
    | true =>
      simp only [d1774, d1603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro965 q selected
  have h5 (q : Pattern) (selected : d1775 q = 2) : d1604 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1775, d1604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1775, d1604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1776 q = 2) : d1605 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1776, d1605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1776, d1605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d1777 q = 2) : d1606 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1777, d1606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1777, d1606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7928 q = 2) : d7881 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7928, d7881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7928, d7881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d7929 q = 2) : d7882 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7929, d7882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7929, d7882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro7955 (p : Pattern) (selected : d7935 p = 2) : d7888 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7930 q = 2) : d7883 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7930, d7883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7954 q selected
    | true =>
      simp only [d7930, d7883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7931 q = 2) : d7884 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7931, d7884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7931, d7884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1785 q = 2) : d1614 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1785, d1614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro967 q selected
    | true =>
      simp only [d1785, d1614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1786 q = 2) : d1615 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1786, d1615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1786, d1615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7932 q = 2) : d7885 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7932, d7885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7932, d7885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7933 q = 2) : d7886 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7933, d7886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7933, d7886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7934 q = 2) : d7887 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7934, d7887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7934, d7887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7935 q = 2) : d7888 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7935, d7888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7935, d7888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7956 (p : Pattern) (selected : d7941 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7883 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7945 q selected
    | true =>
      simp only [d7883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7884 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7938 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7939 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d7940 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d7941 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7957 (p : Pattern) (selected : d7947 p = 2) : d7894 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7909 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7950 q selected
    | true =>
      simp only [d7909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro942 q selected
  have h2 (q : Pattern) (selected : d7910 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7911 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7912 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7916 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7951 q selected
    | true =>
      simp only [d7916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro944 q selected
  have h6 (q : Pattern) (selected : d7917 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7918 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7927 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7953 q selected
    | true =>
      simp only [d7927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7946 q selected
  have h9 (q : Pattern) (selected : d7936 q = 2) : d7889 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7936, d7889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7955 q selected
    | true =>
      simp only [d7936, d7889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro969 q selected
  have h10 (q : Pattern) (selected : d7937 q = 2) : d7890 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7937, d7890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7937, d7890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d7942 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7956 q selected
    | true =>
      simp only [d7942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d7943 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d7943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d7944 q = 2) : d7891 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7944, d7891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d7944, d7891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d7945 q = 2) : d7892 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7945, d7892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7945, d7892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d7946 q = 2) : d7893 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7946, d7893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7946, d7893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d7947 q = 2) : d7894 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7947, d7894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7947, d7894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro7958 (p : Pattern) (selected : d7948 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7883 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7945 q selected
    | true =>
      simp only [d7883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7884 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1614 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro934 q selected
    | true =>
      simp only [d1614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1615 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7885 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7886 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7907 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7948 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7959 (p : Pattern) (selected : d7953 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7883 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7945 q selected
    | true =>
      simp only [d7883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7884 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1614 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro934 q selected
    | true =>
      simp only [d1614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1615 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7885 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7913 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7914 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7953 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7960 (p : Pattern) (selected : d7957 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7921 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7952 q selected
    | true =>
      simp only [d7921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7922 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7883 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7945 q selected
    | true =>
      simp only [d7883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7884 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7923 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7924 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7925 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7957 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7961 (p : Pattern) (selected : d7959 p = 2) : d7897 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7930 q = 2) : d7883 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7930, d7883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7954 q selected
    | true =>
      simp only [d7930, d7883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7931 q = 2) : d7884 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7931, d7884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7931, d7884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1785 q = 2) : d1614 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1785, d1614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro967 q selected
    | true =>
      simp only [d1785, d1614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1786 q = 2) : d1615 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1786, d1615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1786, d1615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7932 q = 2) : d7885 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7932, d7885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7932, d7885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7933 q = 2) : d7886 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7933, d7886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7933, d7886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7934 q = 2) : d7887 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7934, d7887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7934, d7887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7959 q = 2) : d7897 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7959, d7897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7959, d7897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7962 (p : Pattern) (selected : d7962 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7883 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7945 q selected
    | true =>
      simp only [d7883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7884 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7938 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7939 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d7940 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d7962 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7963 (p : Pattern) (selected : d7968 p = 2) : d7903 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7909 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7950 q selected
    | true =>
      simp only [d7909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro942 q selected
  have h2 (q : Pattern) (selected : d7910 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7911 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7912 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7916 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7951 q selected
    | true =>
      simp only [d7916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro944 q selected
  have h6 (q : Pattern) (selected : d7917 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7918 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7927 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7953 q selected
    | true =>
      simp only [d7927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7946 q selected
  have h9 (q : Pattern) (selected : d7936 q = 2) : d7889 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7936, d7889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7955 q selected
    | true =>
      simp only [d7936, d7889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro969 q selected
  have h10 (q : Pattern) (selected : d7937 q = 2) : d7890 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7937, d7890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7937, d7890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d7942 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7956 q selected
    | true =>
      simp only [d7942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d7943 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d7943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d7944 q = 2) : d7891 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7944, d7891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d7944, d7891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d7945 q = 2) : d7892 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7945, d7892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7945, d7892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d7946 q = 2) : d7893 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7946, d7893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7946, d7893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d7949 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7958 q selected
    | true =>
      simp only [d7949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro972 q selected
  have h17 (q : Pattern) (selected : d7950 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d7951 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d7951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d7952 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d7954 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7959 q selected
    | true =>
      simp only [d7954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro974 q selected
  have h21 (q : Pattern) (selected : d7955 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d7956 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d7956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d7958 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7960 q selected
    | true =>
      simp only [d7958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7948 q selected
  have h24 (q : Pattern) (selected : d7960 q = 2) : d7898 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7960, d7898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7961 q selected
    | true =>
      simp only [d7960, d7898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro977 q selected
  have h25 (q : Pattern) (selected : d7961 q = 2) : d7899 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7961, d7899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d7961, d7899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d7963 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7962 q selected
    | true =>
      simp only [d7963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d7964 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d7964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d7965 q = 2) : d7900 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7965, d7900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d7965, d7900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d7966 q = 2) : d7901 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7966, d7901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d7966, d7901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d7967 q = 2) : d7902 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7967, d7902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d7967, d7902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d7968 q = 2) : d7903 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7968, d7903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d7968, d7903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro7964 (p : Pattern) (selected : d7970 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7889 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7946 q selected
    | true =>
      simp only [d7889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro936 q selected
  have h2 (q : Pattern) (selected : d7890 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7891 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7892 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7893 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
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
  have h11 (q : Pattern) (selected : d7970 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro7965 (p : Pattern) (selected : d7977 p = 2) : d99308 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7958 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7960 q selected
    | true =>
      simp only [d7958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7948 q selected
  have h2 (q : Pattern) (selected : d7960 q = 2) : d7898 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7960, d7898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7961 q selected
    | true =>
      simp only [d7960, d7898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro977 q selected
  have h3 (q : Pattern) (selected : d7961 q = 2) : d7899 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7961, d7899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d7961, d7899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d7963 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7962 q selected
    | true =>
      simp only [d7963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d7964 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d7965 q = 2) : d7900 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7965, d7900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7965, d7900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7975 q = 2) : d7901 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7975, d7901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7975, d7901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7976 q = 2) : d7902 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7976, d7902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7976, d7902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d7977 q = 2) : d99308 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7977, d99308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7977, d99308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro7966 (p : Pattern) (selected : d7984 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1874 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro983 q selected
    | true =>
      simp only [d1874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro984 q selected
  have h2 (q : Pattern) (selected : d1875 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1876 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1879 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro984 q selected
    | true =>
      simp only [d1879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro985 q selected
  have h5 (q : Pattern) (selected : d1880 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1881 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d1882 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7983 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d7984 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro7967 (p : Pattern) (selected : d7988 p = 2) : d0 p = 1 := by
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
  have h8 (q : Pattern) (selected : d7987 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d7988 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro7968 (p : Pattern) (selected : d7994 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7985 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7966 q selected
    | true =>
      simp only [d7985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7986 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7989 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7967 q selected
    | true =>
      simp only [d7989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7990 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7991 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7992 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7993 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7994 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7969 (p : Pattern) (selected : d7998 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7989 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7967 q selected
    | true =>
      simp only [d7989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7990 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1908 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro990 q selected
    | true =>
      simp only [d1908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1909 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7995 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7996 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7997 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7998 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7970 (p : Pattern) (selected : d8001 p = 2) : d7988 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1932 q = 2) : d1879 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1932, d1879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro992 q selected
    | true =>
      simp only [d1932, d1879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro993 q selected
  have h2 (q : Pattern) (selected : d1933 q = 2) : d1880 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1933, d1880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1933, d1880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1934 q = 2) : d1881 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1934, d1881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1934, d1881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1941 q = 2) : d1889 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1941, d1889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro993 q selected
    | true =>
      simp only [d1941, d1889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro994 q selected
  have h5 (q : Pattern) (selected : d1942 q = 2) : d1890 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1942, d1890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1942, d1890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1943 q = 2) : d1891 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1943, d1891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1943, d1891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d1944 q = 2) : d1892 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1944, d1892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1944, d1892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d8000 q = 2) : d7987 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8000, d7987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d8000, d7987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d8001 q = 2) : d7988 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8001, d7988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d8001, d7988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro7971 (p : Pattern) (selected : d8007 p = 2) : d7998 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d8002 q = 2) : d7989 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8002, d7989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7970 q selected
    | true =>
      simp only [d8002, d7989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d8003 q = 2) : d7990 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8003, d7990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8003, d7990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1952 q = 2) : d1908 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1952, d1908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro996 q selected
    | true =>
      simp only [d1952, d1908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1953 q = 2) : d1909 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1953, d1909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1953, d1909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d8004 q = 2) : d7995 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8004, d7995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8004, d7995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d8005 q = 2) : d7996 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8005, d7996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d8005, d7996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d8006 q = 2) : d7997 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8006, d7997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d8006, d7997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d8007 q = 2) : d7998 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8007, d7998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d8007, d7998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7972 (p : Pattern) (selected : d8013 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7989 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7967 q selected
    | true =>
      simp only [d7989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7990 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d8010 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d8011 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d8011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d8012 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d8012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d8013 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d8013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7973 (p : Pattern) (selected : d8019 p = 2) : d99319 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7999 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7968 q selected
    | true =>
      simp only [d7999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7969 q selected
  have h2 (q : Pattern) (selected : d8008 q = 2) : d99314 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8008, d99314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7971 q selected
    | true =>
      simp only [d8008, d99314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro998 q selected
  have h3 (q : Pattern) (selected : d8009 q = 2) : d99315 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8009, d99315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d8009, d99315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d8014 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7972 q selected
    | true =>
      simp only [d8014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d8015 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d8015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d8016 q = 2) : d99316 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8016, d99316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d8016, d99316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d8017 q = 2) : d99317 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8017, d99317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8017, d99317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d8018 q = 2) : d99318 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8018, d99318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8018, d99318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d8019 q = 2) : d99319 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8019, d99319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8019, d99319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro7974 (p : Pattern) (selected : d8025 p = 2) : d99325 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d7895 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7947 q selected
  have h2 (q : Pattern) (selected : d7896 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d7896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d7904 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7947 q selected
    | true =>
      simp only [d7904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7949 q selected
  have h4 (q : Pattern) (selected : d7905 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d7906 q = 2) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7969 q = 2) : d7904 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7969, d7904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7957 q selected
    | true =>
      simp only [d7969, d7904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7963 q selected
  have h7 (q : Pattern) (selected : d7971 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7964 q selected
    | true =>
      simp only [d7971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro980 q selected
  have h8 (q : Pattern) (selected : d7972 q = 2) : d7905 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7972, d7905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7972, d7905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d7973 q = 2) : d99306 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7973, d99306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7973, d99306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d7974 q = 2) : d99307 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d7974, d99307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7974, d99307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d7978 q = 2) : d99309 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7978, d99309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7978, d99309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7965 q selected
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
  have h13 (q : Pattern) (selected : d7979 q = 2) : d99310 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7979, d99310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d7979, d99310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d7980 q = 2) : d99311 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7980, d99311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d7980, d99311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d7981 q = 2) : d99312 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d7981, d99312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d7981, d99312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d7982 q = 2) : d99313 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d7982, d99313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d7982, d99313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d8020 q = 2) : d99320 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8020, d99320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8020, d99320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7973 q selected
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
  have h19 (q : Pattern) (selected : d8021 q = 2) : d99321 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8021, d99321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d8021, d99321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d8022 q = 2) : d99322 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d8022, d99322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d8022, d99322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d8023 q = 2) : d99323 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d8023, d99323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d8023, d99323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d8024 q = 2) : d99324 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d8024, d99324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d8024, d99324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d8025 q = 2) : d99325 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d8025, d99325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d8025, d99325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro7975 (p : Pattern) (selected : d8031 p = 2) : d99331 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d8026 q = 2) : d99326 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d8026, d99326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8026, d99326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7974 q selected
  have h2 (q : Pattern) (selected : d8027 q = 2) : d99327 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d8027, d99327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8027, d99327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d8028 q = 2) : d99328 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d8028, d99328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8028, d99328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d8029 q = 2) : d99329 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d8029, d99329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8029, d99329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d8030 q = 2) : d99330 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d8030, d99330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8030, d99330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d8031 q = 2) : d99331 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d8031, d99331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8031, d99331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7976 (p : Pattern) (selected : d8037 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2073 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1018 q selected
    | true =>
      simp only [d2073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1019 q selected
  have h2 (q : Pattern) (selected : d2074 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2075 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2086 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1019 q selected
    | true =>
      simp only [d2086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1021 q selected
  have h5 (q : Pattern) (selected : d2087 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d2088 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d2089 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d8036 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d8036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d8037 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d8037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro7977 (p : Pattern) (selected : d8043 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d8038 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7976 q selected
    | true =>
      simp only [d8038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d8039 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2097 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1023 q selected
    | true =>
      simp only [d2097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2098 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d8040 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d8041 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d8041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d8042 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d8042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d8043 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7978 (p : Pattern) (selected : d8049 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d8044 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7977 q selected
    | true =>
      simp only [d8044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1025 q selected
  have h2 (q : Pattern) (selected : d8045 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d8046 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d8047 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d8048 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d8049 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7979 (p : Pattern) (selected : d8052 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d8038 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7976 q selected
    | true =>
      simp only [d8038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d8039 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2097 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1023 q selected
    | true =>
      simp only [d2097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2098 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d8040 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d8041 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d8041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d8042 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d8042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d8052 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d8052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7980 (p : Pattern) (selected : d8058 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d8044 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7977 q selected
    | true =>
      simp only [d8044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1025 q selected
  have h2 (q : Pattern) (selected : d8045 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d8046 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d8047 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d8048 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d8053 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7979 q selected
    | true =>
      simp only [d8053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1028 q selected
  have h7 (q : Pattern) (selected : d8054 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d8055 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d8055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d8056 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d8057 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d8058 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d8058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro7981 (p : Pattern) (selected : d8063 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d8038 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7976 q selected
    | true =>
      simp only [d8038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d8039 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2097 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1023 q selected
    | true =>
      simp only [d2097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2098 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d8040 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d8041 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d8041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d8062 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d8063 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7982 (p : Pattern) (selected : d8070 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d8038 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7976 q selected
    | true =>
      simp only [d8038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d8039 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2097 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1023 q selected
    | true =>
      simp only [d2097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2098 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d8040 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d8068 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d8069 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d8069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d8070 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7983 (p : Pattern) (selected : d8075 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2150 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1035 q selected
    | true =>
      simp only [d2150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1018 q selected
  have h2 (q : Pattern) (selected : d2151 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2152 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2073 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1018 q selected
    | true =>
      simp only [d2073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1019 q selected
  have h5 (q : Pattern) (selected : d2074 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d2075 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d2153 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d8074 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d8074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d8075 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d8075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro7984 (p : Pattern) (selected : d8081 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d8076 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7983 q selected
    | true =>
      simp only [d8076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d8077 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d8038 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7976 q selected
    | true =>
      simp only [d8038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d8039 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d8078 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d8079 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d8079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d8080 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d8080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d8081 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7985 (p : Pattern) (selected : d8084 p = 2) : d8037 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2239 q = 2) : d2073 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2239, d2073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1052 q selected
    | true =>
      simp only [d2239, d2073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1053 q selected
  have h2 (q : Pattern) (selected : d2240 q = 2) : d2074 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2240, d2074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2240, d2074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2241 q = 2) : d2075 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2241, d2075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2241, d2075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2252 q = 2) : d2086 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2252, d2086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1053 q selected
    | true =>
      simp only [d2252, d2086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1055 q selected
  have h5 (q : Pattern) (selected : d2253 q = 2) : d2087 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2253, d2087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2253, d2087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d2254 q = 2) : d2088 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2254, d2088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2254, d2088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d2255 q = 2) : d2089 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2255, d2089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2255, d2089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d8083 q = 2) : d8036 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8083, d8036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d8083, d8036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d8084 q = 2) : d8037 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8084, d8037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d8084, d8037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro7986 (p : Pattern) (selected : d8090 p = 2) : d8043 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d8085 q = 2) : d8038 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8085, d8038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7985 q selected
    | true =>
      simp only [d8085, d8038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d8086 q = 2) : d8039 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8086, d8039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8086, d8039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2263 q = 2) : d2097 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2263, d2097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1057 q selected
    | true =>
      simp only [d2263, d2097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2264 q = 2) : d2098 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2264, d2098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2264, d2098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d8087 q = 2) : d8040 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8087, d8040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8087, d8040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d8088 q = 2) : d8041 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8088, d8041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d8088, d8041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d8089 q = 2) : d8042 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8089, d8042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d8089, d8042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d8090 q = 2) : d8043 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8090, d8043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8090, d8043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7987 (p : Pattern) (selected : d8096 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d8038 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7976 q selected
    | true =>
      simp only [d8038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d8039 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d8093 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d8094 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d8094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d8095 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d8095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d8096 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7988 (p : Pattern) (selected : d8102 p = 2) : d8049 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d8064 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7981 q selected
    | true =>
      simp only [d8064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1031 q selected
  have h2 (q : Pattern) (selected : d8065 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d8066 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d8067 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d8071 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7982 q selected
    | true =>
      simp only [d8071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1033 q selected
  have h6 (q : Pattern) (selected : d8072 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d8073 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d8073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d8082 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7984 q selected
    | true =>
      simp only [d8082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7977 q selected
  have h9 (q : Pattern) (selected : d8091 q = 2) : d8044 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8091, d8044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7986 q selected
    | true =>
      simp only [d8091, d8044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1059 q selected
  have h10 (q : Pattern) (selected : d8092 q = 2) : d8045 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8092, d8045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d8092, d8045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d8097 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7987 q selected
    | true =>
      simp only [d8097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d8098 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d8098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d8099 q = 2) : d8046 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8099, d8046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d8099, d8046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d8100 q = 2) : d8047 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8100, d8047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d8100, d8047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d8101 q = 2) : d8048 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8101, d8048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d8101, d8048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d8102 q = 2) : d8049 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8102, d8049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8102, d8049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro7989 (p : Pattern) (selected : d8103 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d8038 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7976 q selected
    | true =>
      simp only [d8038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d8039 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2097 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1023 q selected
    | true =>
      simp only [d2097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2098 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d8040 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d8041 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d8041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d8062 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d8103 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d8103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7990 (p : Pattern) (selected : d8108 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d8038 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7976 q selected
    | true =>
      simp only [d8038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d8039 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2097 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1023 q selected
    | true =>
      simp only [d2097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2098 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d8040 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d8068 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d8069 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d8069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d8108 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d8108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7991 (p : Pattern) (selected : d8112 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d8076 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7983 q selected
    | true =>
      simp only [d8076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d8077 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d8038 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7976 q selected
    | true =>
      simp only [d8038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d8039 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d8078 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d8079 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d8079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d8080 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d8080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d8112 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d8112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7992 (p : Pattern) (selected : d8114 p = 2) : d8052 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d8085 q = 2) : d8038 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8085, d8038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7985 q selected
    | true =>
      simp only [d8085, d8038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d8086 q = 2) : d8039 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8086, d8039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8086, d8039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2263 q = 2) : d2097 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2263, d2097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1057 q selected
    | true =>
      simp only [d2263, d2097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2264 q = 2) : d2098 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2264, d2098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2264, d2098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d8087 q = 2) : d8040 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8087, d8040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8087, d8040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d8088 q = 2) : d8041 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8088, d8041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d8088, d8041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d8089 q = 2) : d8042 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8089, d8042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d8089, d8042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d8114 q = 2) : d8052 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8114, d8052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d8114, d8052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7993 (p : Pattern) (selected : d8117 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d8038 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7976 q selected
    | true =>
      simp only [d8038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d8039 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d8093 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d8094 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d8094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d8095 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d8095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d8117 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d8117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7994 (p : Pattern) (selected : d8123 p = 2) : d8058 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d8064 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7981 q selected
    | true =>
      simp only [d8064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1031 q selected
  have h2 (q : Pattern) (selected : d8065 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d8066 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d8067 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d8071 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7982 q selected
    | true =>
      simp only [d8071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1033 q selected
  have h6 (q : Pattern) (selected : d8072 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d8073 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d8073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d8082 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7984 q selected
    | true =>
      simp only [d8082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7977 q selected
  have h9 (q : Pattern) (selected : d8091 q = 2) : d8044 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8091, d8044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7986 q selected
    | true =>
      simp only [d8091, d8044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1059 q selected
  have h10 (q : Pattern) (selected : d8092 q = 2) : d8045 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8092, d8045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d8092, d8045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d8097 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7987 q selected
    | true =>
      simp only [d8097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d8098 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d8098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d8099 q = 2) : d8046 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8099, d8046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d8099, d8046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d8100 q = 2) : d8047 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8100, d8047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d8100, d8047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d8101 q = 2) : d8048 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8101, d8048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d8101, d8048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d8104 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7989 q selected
    | true =>
      simp only [d8104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1062 q selected
  have h17 (q : Pattern) (selected : d8105 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d8106 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d8106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d8107 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d8109 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7990 q selected
    | true =>
      simp only [d8109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1064 q selected
  have h21 (q : Pattern) (selected : d8110 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d8111 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d8111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d8113 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7991 q selected
    | true =>
      simp only [d8113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7979 q selected
  have h24 (q : Pattern) (selected : d8115 q = 2) : d8053 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8115, d8053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7992 q selected
    | true =>
      simp only [d8115, d8053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1067 q selected
  have h25 (q : Pattern) (selected : d8116 q = 2) : d8054 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8116, d8054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d8116, d8054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d8118 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7993 q selected
    | true =>
      simp only [d8118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d8119 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d8119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d8120 q = 2) : d8055 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8120, d8055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d8120, d8055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d8121 q = 2) : d8056 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8121, d8056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d8121, d8056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d8122 q = 2) : d8057 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8122, d8057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d8122, d8057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d8123 q = 2) : d8058 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8123, d8058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d8123, d8058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro7995 (p : Pattern) (selected : d8125 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d8044 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7977 q selected
    | true =>
      simp only [d8044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1025 q selected
  have h2 (q : Pattern) (selected : d8045 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d8046 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d8047 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d8048 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
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
  have h11 (q : Pattern) (selected : d8125 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d8125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro7996 (p : Pattern) (selected : d8132 p = 2) : d99338 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d8113 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7991 q selected
    | true =>
      simp only [d8113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7979 q selected
  have h2 (q : Pattern) (selected : d8115 q = 2) : d8053 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8115, d8053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7992 q selected
    | true =>
      simp only [d8115, d8053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1067 q selected
  have h3 (q : Pattern) (selected : d8116 q = 2) : d8054 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8116, d8054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d8116, d8054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d8118 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7993 q selected
    | true =>
      simp only [d8118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d8119 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d8119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d8120 q = 2) : d8055 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8120, d8055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d8120, d8055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d8130 q = 2) : d8056 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8130, d8056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8130, d8056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d8131 q = 2) : d8057 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8131, d8057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8131, d8057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d8132 q = 2) : d99338 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8132, d99338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8132, d99338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro7997 (p : Pattern) (selected : d8139 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2352 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1073 q selected
    | true =>
      simp only [d2352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1074 q selected
  have h2 (q : Pattern) (selected : d2353 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2354 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2357 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1074 q selected
    | true =>
      simp only [d2357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1075 q selected
  have h5 (q : Pattern) (selected : d2358 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d2359 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d2360 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d8138 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d8138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d8139 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d8139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro7998 (p : Pattern) (selected : d8143 p = 2) : d0 p = 1 := by
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
  have h8 (q : Pattern) (selected : d8142 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d8142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d8143 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d8143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro7999 (p : Pattern) (selected : d8149 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d8140 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7997 q selected
    | true =>
      simp only [d8140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d8141 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d8144 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7998 q selected
    | true =>
      simp only [d8144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d8145 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d8146 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d8147 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d8147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d8148 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d8148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d8149 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d8149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
end NetHack.Soko22Hazard87
