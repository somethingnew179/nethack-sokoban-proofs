import NetHack.Soko22Hazard87.EqIntroBlocks0154
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem eqIntro38750 (p : Pattern) (selected : d368340 p = 0) : d369037 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368335 q = 0) : d369032 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d368335, d369032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368335, d369032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38749 q selected
  have h2 (q : Pattern) (selected : d368336 q = 0) : d369033 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d368336, d369033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368336, d369033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368337 q = 0) : d369034 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d368337, d369034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368337, d369034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368338 q = 0) : d369035 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d368338, d369035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368338, d369035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d368339 q = 0) : d369036 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d368339, d369036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368339, d369036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368340 q = 0) : d369037 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d368340, d369037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368340, d369037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro38751 (p : Pattern) (selected : d368345 p = 0) : d369042 p = 1 := by
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
  have h3 (q : Pattern) (selected : d308 q = 0) : d52107 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d308, d52107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d308, d52107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1523 q = 0) : d52964 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1523, d52964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1523, d52964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d218587 q = 0) : d220585 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d218587, d220585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d218587, d220585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d368345 q = 0) : d369042 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d368345, d369042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368345, d369042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38752 (p : Pattern) (selected : d368350 p = 0) : d369047 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368346 q = 0) : d369043 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d368346, d369043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368346, d369043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38751 q selected
  have h2 (q : Pattern) (selected : d368347 q = 0) : d369044 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d368347, d369044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368347, d369044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d368348 q = 0) : d369045 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d368348, d369045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368348, d369045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368349 q = 0) : d369046 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d368349, d369046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368349, d369046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368350 q = 0) : d369047 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d368350, d369047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368350, d369047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro38753 (p : Pattern) (selected : d368356 p = 0) : d369053 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368346 q = 0) : d369043 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d368346, d369043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368346, d369043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38751 q selected
  have h2 (q : Pattern) (selected : d368347 q = 0) : d369044 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d368347, d369044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368347, d369044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d368348 q = 0) : d369045 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d368348, d369045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368348, d369045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368349 q = 0) : d369046 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d368349, d369046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368349, d369046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d218652 q = 0) : d220650 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d218652, d220650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218652, d220650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21544 q selected
  have h6 (q : Pattern) (selected : d218653 q = 0) : d220651 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d218653, d220651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d218653, d220651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d218654 q = 0) : d220652 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d218654, d220652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21544 q selected
    | true =>
      simp only [d218654, d220652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d218655 q = 0) : d220653 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d218655, d220653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d218655, d220653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d218656 q = 0) : d220654 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d218656, d220654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d218656, d220654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d218657 q = 0) : d220655 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d218657, d220655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d218657, d220655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d368356 q = 0) : d369053 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d368356, d369053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368356, d369053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro38754 (p : Pattern) (selected : d368362 p = 0) : d369059 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368351 q = 0) : d369048 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368351, d369048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38752 q selected
    | true =>
      simp only [d368351, d369048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368352 q = 0) : d369049 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368352, d369049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368352, d369049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d368353 q = 0) : d369050 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368353, d369050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368353, d369050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368354 q = 0) : d369051 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368354, d369051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368354, d369051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368355 q = 0) : d369052 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368355, d369052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368355, d369052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368357 q = 0) : d369054 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368357, d369054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38753 q selected
    | true =>
      simp only [d368357, d369054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d368358 q = 0) : d369055 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368358, d369055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d368358, d369055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d368359 q = 0) : d369056 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368359, d369056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368359, d369056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d368360 q = 0) : d369057 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368360, d369057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d368360, d369057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d368361 q = 0) : d369058 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368361, d369058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368361, d369058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d368362 q = 0) : d369059 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d368362, d369059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368362, d369059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro38755 (p : Pattern) (selected : d368364 p = 0) : d369061 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368351 q = 0) : d369048 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368351, d369048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38752 q selected
    | true =>
      simp only [d368351, d369048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368352 q = 0) : d369049 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368352, d369049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368352, d369049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d368353 q = 0) : d369050 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368353, d369050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368353, d369050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368354 q = 0) : d369051 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368354, d369051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368354, d369051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368357 q = 0) : d369054 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368357, d369054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38753 q selected
    | true =>
      simp only [d368357, d369054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d368358 q = 0) : d369055 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368358, d369055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368358, d369055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d368359 q = 0) : d369056 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368359, d369056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368359, d369056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d368360 q = 0) : d369057 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368360, d369057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368360, d369057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d368361 q = 0) : d369058 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368361, d369058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368361, d369058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d368363 q = 0) : d369060 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368363, d369060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d368363, d369060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d368364 q = 0) : d369061 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d368364, d369061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d368364, d369061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro38756 (p : Pattern) (selected : d368368 p = 0) : d369065 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368357 q = 0) : d369054 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368357, d369054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38753 q selected
    | true =>
      simp only [d368357, d369054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368358 q = 0) : d369055 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368358, d369055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368358, d369055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d368359 q = 0) : d369056 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368359, d369056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368359, d369056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368360 q = 0) : d369057 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368360, d369057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368360, d369057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368363 q = 0) : d369060 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368363, d369060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368363, d369060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d218659 q = 0) : d220657 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d218659, d220657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21548 q selected
    | true =>
      simp only [d218659, d220657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d218660 q = 0) : d220658 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d218660, d220658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d218660, d220658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d218661 q = 0) : d220659 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d218661, d220659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218661, d220659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d218662 q = 0) : d220660 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d218662, d220660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d218662, d220660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d218663 q = 0) : d220661 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d218663, d220661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d218663, d220661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d368368 q = 0) : d369065 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d368368, d369065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368368, d369065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro38757 (p : Pattern) (selected : d368375 p = 0) : d369072 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368365 q = 0) : d369062 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d368365, d369062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38754 q selected
    | true =>
      simp only [d368365, d369062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38755 q selected
  have h2 (q : Pattern) (selected : d368366 q = 0) : d369063 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d368366, d369063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368366, d369063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368367 q = 0) : d369064 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d368367, d369064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368367, d369064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368369 q = 0) : d369066 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d368369, d369066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38755 q selected
    | true =>
      simp only [d368369, d369066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38756 q selected
  have h5 (q : Pattern) (selected : d368370 q = 0) : d369067 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d368370, d369067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368370, d369067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368371 q = 0) : d369068 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d368371, d369068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368371, d369068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d368372 q = 0) : d369069 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d368372, d369069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368372, d369069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d368373 q = 0) : d369070 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d368373, d369070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d368373, d369070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d368374 q = 0) : d369071 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d368374, d369071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368374, d369071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d368375 q = 0) : d369072 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d368375, d369072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d368375, d369072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro38758 (p : Pattern) (selected : d368379 p = 0) : d369076 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368369 q = 0) : d369066 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d368369, d369066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38755 q selected
    | true =>
      simp only [d368369, d369066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38756 q selected
  have h2 (q : Pattern) (selected : d368370 q = 0) : d369067 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d368370, d369067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368370, d369067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368371 q = 0) : d369068 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d368371, d369068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368371, d369068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368373 q = 0) : d369070 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d368373, d369070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368373, d369070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368378 q = 0) : d369075 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d368378, d369075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368378, d369075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d368379 q = 0) : d369076 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d368379, d369076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368379, d369076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38759 (p : Pattern) (selected : d368385 p = 0) : d369082 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368376 q = 0) : d369073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368376, d369073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38757 q selected
    | true =>
      simp only [d368376, d369073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368377 q = 0) : d369074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368377, d369074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368377, d369074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368380 q = 0) : d369077 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368380, d369077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38758 q selected
    | true =>
      simp only [d368380, d369077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368381 q = 0) : d369078 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368381, d369078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368381, d369078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d368382 q = 0) : d369079 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d368382, d369079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368382, d369079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368383 q = 0) : d369080 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d368383, d369080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368383, d369080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d368384 q = 0) : d369081 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d368384, d369081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d368384, d369081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d368385 q = 0) : d369082 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d368385, d369082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368385, d369082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro38760 (p : Pattern) (selected : d368389 p = 0) : d369086 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368380 q = 0) : d369077 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368380, d369077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38758 q selected
    | true =>
      simp only [d368380, d369077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368381 q = 0) : d369078 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368381, d369078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368381, d369078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368386 q = 0) : d369083 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d368386, d369083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368386, d369083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368387 q = 0) : d369084 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d368387, d369084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368387, d369084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368388 q = 0) : d369085 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d368388, d369085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368388, d369085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d368389 q = 0) : d369086 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d368389, d369086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368389, d369086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro38761 (p : Pattern) (selected : d368395 p = 0) : d369092 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368390 q = 0) : d369087 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368390, d369087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38759 q selected
    | true =>
      simp only [d368390, d369087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38760 q selected
  have h2 (q : Pattern) (selected : d368391 q = 0) : d369088 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368391, d369088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368391, d369088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368392 q = 0) : d369089 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d368392, d369089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368392, d369089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368393 q = 0) : d369090 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d368393, d369090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368393, d369090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d368394 q = 0) : d369091 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d368394, d369091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368394, d369091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368395 q = 0) : d369092 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d368395, d369092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368395, d369092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro38762 (p : Pattern) (selected : d368398 p = 0) : d369095 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368376 q = 0) : d369073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368376, d369073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38757 q selected
    | true =>
      simp only [d368376, d369073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368377 q = 0) : d369074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368377, d369074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368377, d369074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368380 q = 0) : d369077 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368380, d369077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38758 q selected
    | true =>
      simp only [d368380, d369077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368381 q = 0) : d369078 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368381, d369078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368381, d369078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d368382 q = 0) : d369079 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d368382, d369079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368382, d369079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368383 q = 0) : d369080 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d368383, d369080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368383, d369080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d368384 q = 0) : d369081 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d368384, d369081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d368384, d369081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d368398 q = 0) : d369095 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d368398, d369095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368398, d369095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro38763 (p : Pattern) (selected : d368399 p = 0) : d369096 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368380 q = 0) : d369077 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368380, d369077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38758 q selected
    | true =>
      simp only [d368380, d369077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368381 q = 0) : d369078 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368381, d369078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368381, d369078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368386 q = 0) : d369083 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d368386, d369083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368386, d369083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368387 q = 0) : d369084 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d368387, d369084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368387, d369084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368388 q = 0) : d369085 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d368388, d369085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368388, d369085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d368399 q = 0) : d369096 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d368399, d369096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368399, d369096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38764 (p : Pattern) (selected : d368405 p = 0) : d369102 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368390 q = 0) : d369087 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368390, d369087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38759 q selected
    | true =>
      simp only [d368390, d369087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38760 q selected
  have h2 (q : Pattern) (selected : d368391 q = 0) : d369088 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368391, d369088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368391, d369088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368392 q = 0) : d369089 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d368392, d369089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368392, d369089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368393 q = 0) : d369090 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d368393, d369090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368393, d369090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d368394 q = 0) : d369091 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d368394, d369091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368394, d369091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368400 q = 0) : d369097 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368400, d369097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38762 q selected
    | true =>
      simp only [d368400, d369097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38763 q selected
  have h7 (q : Pattern) (selected : d368401 q = 0) : d369098 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368401, d369098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368401, d369098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d368402 q = 0) : d369099 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d368402, d369099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368402, d369099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d368403 q = 0) : d369100 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d368403, d369100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368403, d369100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d368404 q = 0) : d369101 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d368404, d369101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368404, d369101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d368405 q = 0) : d369102 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d368405, d369102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368405, d369102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro38765 (p : Pattern) (selected : d368410 p = 0) : d369107 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368376 q = 0) : d369073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368376, d369073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38757 q selected
    | true =>
      simp only [d368376, d369073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368377 q = 0) : d369074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368377, d369074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368377, d369074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368380 q = 0) : d369077 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368380, d369077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38758 q selected
    | true =>
      simp only [d368380, d369077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368381 q = 0) : d369078 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368381, d369078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368381, d369078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d368382 q = 0) : d369079 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d368382, d369079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368382, d369079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368383 q = 0) : d369080 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d368383, d369080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368383, d369080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d368409 q = 0) : d369106 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d368409, d369106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368409, d369106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d368410 q = 0) : d369107 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d368410, d369107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368410, d369107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro38766 (p : Pattern) (selected : d368412 p = 0) : d369109 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368380 q = 0) : d369077 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368380, d369077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38758 q selected
    | true =>
      simp only [d368380, d369077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368381 q = 0) : d369078 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368381, d369078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368381, d369078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368386 q = 0) : d369083 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d368386, d369083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368386, d369083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368387 q = 0) : d369084 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d368387, d369084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368387, d369084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368411 q = 0) : d369108 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d368411, d369108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368411, d369108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368412 q = 0) : d369109 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d368412, d369109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368412, d369109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro38767 (p : Pattern) (selected : d368419 p = 0) : d369116 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368376 q = 0) : d369073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368376, d369073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38757 q selected
    | true =>
      simp only [d368376, d369073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368377 q = 0) : d369074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368377, d369074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368377, d369074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368380 q = 0) : d369077 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368380, d369077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38758 q selected
    | true =>
      simp only [d368380, d369077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368381 q = 0) : d369078 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368381, d369078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368381, d369078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d368382 q = 0) : d369079 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d368382, d369079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368382, d369079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368417 q = 0) : d369114 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d368417, d369114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368417, d369114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d368418 q = 0) : d369115 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d368418, d369115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d368418, d369115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d368419 q = 0) : d369116 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d368419, d369116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368419, d369116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro38768 (p : Pattern) (selected : d368422 p = 0) : d369119 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368380 q = 0) : d369077 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368380, d369077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38758 q selected
    | true =>
      simp only [d368380, d369077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368381 q = 0) : d369078 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368381, d369078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368381, d369078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368386 q = 0) : d369083 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d368386, d369083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368386, d369083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368420 q = 0) : d369117 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d368420, d369117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368420, d369117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d368421 q = 0) : d369118 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d368421, d369118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368421, d369118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d368422 q = 0) : d369119 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d368422, d369119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368422, d369119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro38769 (p : Pattern) (selected : d368426 p = 0) : d369123 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368351 q = 0) : d369048 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368351, d369048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38752 q selected
    | true =>
      simp only [d368351, d369048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368352 q = 0) : d369049 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368352, d369049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368352, d369049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d368353 q = 0) : d369050 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368353, d369050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368353, d369050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368354 q = 0) : d369051 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368354, d369051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368354, d369051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368355 q = 0) : d369052 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368355, d369052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368355, d369052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368426 q = 0) : d369123 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d368426, d369123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368426, d369123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro38770 (p : Pattern) (selected : d368432 p = 0) : d369129 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368427 q = 0) : d369124 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d368427, d369124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38769 q selected
    | true =>
      simp only [d368427, d369124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38754 q selected
  have h2 (q : Pattern) (selected : d368428 q = 0) : d369125 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d368428, d369125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368428, d369125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368429 q = 0) : d369126 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d368429, d369126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368429, d369126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368365 q = 0) : d369062 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d368365, d369062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38754 q selected
    | true =>
      simp only [d368365, d369062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38755 q selected
  have h5 (q : Pattern) (selected : d368366 q = 0) : d369063 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d368366, d369063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368366, d369063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368367 q = 0) : d369064 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d368367, d369064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368367, d369064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d368430 q = 0) : d369127 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d368430, d369127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368430, d369127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d368369 q = 0) : d369066 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d368369, d369066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38755 q selected
    | true =>
      simp only [d368369, d369066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38756 q selected
  have h9 (q : Pattern) (selected : d368370 q = 0) : d369067 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d368370, d369067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368370, d369067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d368371 q = 0) : d369068 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d368371, d369068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368371, d369068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d368372 q = 0) : d369069 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d368372, d369069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d368372, d369069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d368431 q = 0) : d369128 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d368431, d369128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368431, d369128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d368432 q = 0) : d369129 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d368432, d369129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d368432, d369129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro38771 (p : Pattern) (selected : d368438 p = 0) : d369135 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368433 q = 0) : d369130 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368433, d369130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38770 q selected
    | true =>
      simp only [d368433, d369130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368434 q = 0) : d369131 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368434, d369131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368434, d369131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368376 q = 0) : d369073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368376, d369073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38757 q selected
    | true =>
      simp only [d368376, d369073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368377 q = 0) : d369074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368377, d369074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368377, d369074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d368435 q = 0) : d369132 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d368435, d369132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368435, d369132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368436 q = 0) : d369133 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d368436, d369133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368436, d369133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d368437 q = 0) : d369134 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d368437, d369134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d368437, d369134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d368438 q = 0) : d369135 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d368438, d369135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368438, d369135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro38772 (p : Pattern) (selected : d368440 p = 0) : d369042 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2 q = 0) : d0 q = 1 := by
    change (2 : Int) = 0 at selected
    omega
  have h2 (q : Pattern) (selected : d338 q = 0) : d13 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d338, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d338, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d563 q = 0) : d52107 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d563, d52107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d563, d52107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1691 q = 0) : d52964 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1691, d52964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1691, d52964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d218775 q = 0) : d220585 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d218775, d220585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d218775, d220585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d368440 q = 0) : d369042 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d368440, d369042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368440, d369042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38773 (p : Pattern) (selected : d368445 p = 0) : d369047 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368441 q = 0) : d369043 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d368441, d369043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368441, d369043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38772 q selected
  have h2 (q : Pattern) (selected : d368442 q = 0) : d369044 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d368442, d369044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368442, d369044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d368443 q = 0) : d369045 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d368443, d369045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368443, d369045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368444 q = 0) : d369046 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d368444, d369046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368444, d369046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368445 q = 0) : d369047 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d368445, d369047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368445, d369047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro38774 (p : Pattern) (selected : d368451 p = 0) : d369053 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368441 q = 0) : d369043 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d368441, d369043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368441, d369043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38772 q selected
  have h2 (q : Pattern) (selected : d368442 q = 0) : d369044 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d368442, d369044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368442, d369044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d368443 q = 0) : d369045 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d368443, d369045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368443, d369045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368444 q = 0) : d369046 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d368444, d369046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368444, d369046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d218840 q = 0) : d220650 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d218840, d220650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218840, d220650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21582 q selected
  have h6 (q : Pattern) (selected : d218841 q = 0) : d220651 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d218841, d220651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d218841, d220651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d218842 q = 0) : d220652 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d218842, d220652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21582 q selected
    | true =>
      simp only [d218842, d220652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d218843 q = 0) : d220653 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d218843, d220653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d218843, d220653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d218844 q = 0) : d220654 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d218844, d220654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d218844, d220654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d218845 q = 0) : d220655 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d218845, d220655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d218845, d220655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d368451 q = 0) : d369053 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d368451, d369053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368451, d369053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro38775 (p : Pattern) (selected : d368457 p = 0) : d369059 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368446 q = 0) : d369048 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368446, d369048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38773 q selected
    | true =>
      simp only [d368446, d369048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368447 q = 0) : d369049 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368447, d369049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368447, d369049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d368448 q = 0) : d369050 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368448, d369050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368448, d369050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368449 q = 0) : d369051 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368449, d369051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368449, d369051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368450 q = 0) : d369052 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368450, d369052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368450, d369052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368452 q = 0) : d369054 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368452, d369054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38774 q selected
    | true =>
      simp only [d368452, d369054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d368453 q = 0) : d369055 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368453, d369055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d368453, d369055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d368454 q = 0) : d369056 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368454, d369056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368454, d369056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d368455 q = 0) : d369057 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368455, d369057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d368455, d369057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d368456 q = 0) : d369058 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368456, d369058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368456, d369058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d368457 q = 0) : d369059 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d368457, d369059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368457, d369059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro38776 (p : Pattern) (selected : d368459 p = 0) : d369061 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368446 q = 0) : d369048 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368446, d369048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38773 q selected
    | true =>
      simp only [d368446, d369048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368447 q = 0) : d369049 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368447, d369049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368447, d369049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d368448 q = 0) : d369050 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368448, d369050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368448, d369050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368449 q = 0) : d369051 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368449, d369051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368449, d369051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368452 q = 0) : d369054 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368452, d369054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38774 q selected
    | true =>
      simp only [d368452, d369054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d368453 q = 0) : d369055 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368453, d369055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368453, d369055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d368454 q = 0) : d369056 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368454, d369056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368454, d369056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d368455 q = 0) : d369057 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368455, d369057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368455, d369057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d368456 q = 0) : d369058 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368456, d369058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368456, d369058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d368458 q = 0) : d369060 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368458, d369060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d368458, d369060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d368459 q = 0) : d369061 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d368459, d369061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d368459, d369061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro38777 (p : Pattern) (selected : d368463 p = 0) : d369065 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368452 q = 0) : d369054 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368452, d369054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38774 q selected
    | true =>
      simp only [d368452, d369054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368453 q = 0) : d369055 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368453, d369055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368453, d369055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d368454 q = 0) : d369056 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368454, d369056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368454, d369056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368455 q = 0) : d369057 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368455, d369057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368455, d369057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368458 q = 0) : d369060 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368458, d369060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368458, d369060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d218847 q = 0) : d220657 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d218847, d220657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21586 q selected
    | true =>
      simp only [d218847, d220657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d218848 q = 0) : d220658 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d218848, d220658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d218848, d220658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d218849 q = 0) : d220659 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d218849, d220659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218849, d220659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d218850 q = 0) : d220660 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d218850, d220660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d218850, d220660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d218851 q = 0) : d220661 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d218851, d220661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d218851, d220661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d368463 q = 0) : d369065 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d368463, d369065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368463, d369065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro38778 (p : Pattern) (selected : d368470 p = 0) : d369072 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368460 q = 0) : d369062 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d368460, d369062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38775 q selected
    | true =>
      simp only [d368460, d369062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38776 q selected
  have h2 (q : Pattern) (selected : d368461 q = 0) : d369063 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d368461, d369063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368461, d369063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368462 q = 0) : d369064 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d368462, d369064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368462, d369064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368464 q = 0) : d369066 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d368464, d369066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38776 q selected
    | true =>
      simp only [d368464, d369066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38777 q selected
  have h5 (q : Pattern) (selected : d368465 q = 0) : d369067 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d368465, d369067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368465, d369067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368466 q = 0) : d369068 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d368466, d369068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368466, d369068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d368467 q = 0) : d369069 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d368467, d369069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368467, d369069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d368468 q = 0) : d369070 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d368468, d369070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d368468, d369070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d368469 q = 0) : d369071 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d368469, d369071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368469, d369071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d368470 q = 0) : d369072 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d368470, d369072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d368470, d369072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro38779 (p : Pattern) (selected : d368474 p = 0) : d369076 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368464 q = 0) : d369066 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d368464, d369066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38776 q selected
    | true =>
      simp only [d368464, d369066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38777 q selected
  have h2 (q : Pattern) (selected : d368465 q = 0) : d369067 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d368465, d369067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368465, d369067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368466 q = 0) : d369068 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d368466, d369068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368466, d369068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368468 q = 0) : d369070 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d368468, d369070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368468, d369070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368473 q = 0) : d369075 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d368473, d369075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368473, d369075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d368474 q = 0) : d369076 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d368474, d369076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368474, d369076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38780 (p : Pattern) (selected : d368480 p = 0) : d369082 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368471 q = 0) : d369073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368471, d369073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38778 q selected
    | true =>
      simp only [d368471, d369073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368472 q = 0) : d369074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368472, d369074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368472, d369074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368475 q = 0) : d369077 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368475, d369077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38779 q selected
    | true =>
      simp only [d368475, d369077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368476 q = 0) : d369078 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368476, d369078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368476, d369078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d368477 q = 0) : d369079 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d368477, d369079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368477, d369079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368478 q = 0) : d369080 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d368478, d369080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368478, d369080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d368479 q = 0) : d369081 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d368479, d369081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d368479, d369081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d368480 q = 0) : d369082 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d368480, d369082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368480, d369082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro38781 (p : Pattern) (selected : d368484 p = 0) : d369086 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368475 q = 0) : d369077 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368475, d369077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38779 q selected
    | true =>
      simp only [d368475, d369077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368476 q = 0) : d369078 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368476, d369078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368476, d369078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368481 q = 0) : d369083 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d368481, d369083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368481, d369083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368482 q = 0) : d369084 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d368482, d369084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368482, d369084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368483 q = 0) : d369085 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d368483, d369085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368483, d369085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d368484 q = 0) : d369086 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d368484, d369086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368484, d369086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro38782 (p : Pattern) (selected : d368487 p = 0) : d369138 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368346 q = 0) : d369043 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d368346, d369043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368346, d369043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38751 q selected
  have h2 (q : Pattern) (selected : d368347 q = 0) : d369044 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d368347, d369044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368347, d369044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d368348 q = 0) : d369045 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d368348, d369045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368348, d369045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368349 q = 0) : d369046 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d368349, d369046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368349, d369046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368487 q = 0) : d369138 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d368487, d369138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368487, d369138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro38783 (p : Pattern) (selected : d368493 p = 0) : d369144 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368351 q = 0) : d369048 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368351, d369048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38752 q selected
    | true =>
      simp only [d368351, d369048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368352 q = 0) : d369049 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368352, d369049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368352, d369049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d368353 q = 0) : d369050 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368353, d369050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368353, d369050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368354 q = 0) : d369051 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368354, d369051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368354, d369051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368357 q = 0) : d369054 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368357, d369054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38753 q selected
    | true =>
      simp only [d368357, d369054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d368358 q = 0) : d369055 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368358, d369055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368358, d369055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d368359 q = 0) : d369056 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368359, d369056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368359, d369056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d368360 q = 0) : d369057 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368360, d369057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368360, d369057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d368361 q = 0) : d369058 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368361, d369058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368361, d369058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d368488 q = 0) : d369139 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368488, d369139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38782 q selected
    | true =>
      simp only [d368488, d369139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d368489 q = 0) : d369140 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368489, d369140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d368489, d369140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d368490 q = 0) : d369141 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368490, d369141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368490, d369141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d368491 q = 0) : d369142 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368491, d369142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d368491, d369142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d368492 q = 0) : d369143 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368492, d369143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d368492, d369143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d368493 q = 0) : d369144 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d368493, d369144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d368493, d369144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro38784 (p : Pattern) (selected : d368494 p = 0) : d369145 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368488 q = 0) : d369139 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368488, d369139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38782 q selected
    | true =>
      simp only [d368488, d369139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368489 q = 0) : d369140 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368489, d369140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368489, d369140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d368490 q = 0) : d369141 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368490, d369141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368490, d369141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368491 q = 0) : d369142 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368491, d369142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368491, d369142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368492 q = 0) : d369143 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368492, d369143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368492, d369143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d368494 q = 0) : d369145 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d368494, d369145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368494, d369145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38785 (p : Pattern) (selected : d368500 p = 0) : d369151 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368365 q = 0) : d369062 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d368365, d369062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38754 q selected
    | true =>
      simp only [d368365, d369062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38755 q selected
  have h2 (q : Pattern) (selected : d368366 q = 0) : d369063 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d368366, d369063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368366, d369063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368367 q = 0) : d369064 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d368367, d369064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368367, d369064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368369 q = 0) : d369066 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d368369, d369066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38755 q selected
    | true =>
      simp only [d368369, d369066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38756 q selected
  have h5 (q : Pattern) (selected : d368370 q = 0) : d369067 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d368370, d369067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368370, d369067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368371 q = 0) : d369068 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d368371, d369068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368371, d369068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d368372 q = 0) : d369069 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d368372, d369069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368372, d369069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d368495 q = 0) : d369146 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d368495, d369146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38783 q selected
    | true =>
      simp only [d368495, d369146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38784 q selected
  have h9 (q : Pattern) (selected : d368496 q = 0) : d369147 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d368496, d369147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368496, d369147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d368497 q = 0) : d369148 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d368497, d369148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368497, d369148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d368498 q = 0) : d369149 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d368498, d369149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d368498, d369149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d368499 q = 0) : d369150 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d368499, d369150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368499, d369150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d368500 q = 0) : d369151 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d368500, d369151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d368500, d369151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro38786 (p : Pattern) (selected : d368506 p = 0) : d369157 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368501 q = 0) : d369152 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368501, d369152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38785 q selected
    | true =>
      simp only [d368501, d369152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368502 q = 0) : d369153 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368502, d369153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368502, d369153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368503 q = 0) : d369154 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d368503, d369154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368503, d369154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368504 q = 0) : d369155 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d368504, d369155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368504, d369155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368505 q = 0) : d369156 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d368505, d369156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368505, d369156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d368506 q = 0) : d369157 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d368506, d369157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368506, d369157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro38787 (p : Pattern) (selected : d368512 p = 0) : d369163 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368413 q = 0) : d369110 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368413, d369110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38765 q selected
    | true =>
      simp only [d368413, d369110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38766 q selected
  have h2 (q : Pattern) (selected : d368414 q = 0) : d369111 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368414, d369111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368414, d369111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368415 q = 0) : d369112 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d368415, d369112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368415, d369112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368416 q = 0) : d369113 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d368416, d369113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368416, d369113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d368423 q = 0) : d369120 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368423, d369120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38767 q selected
    | true =>
      simp only [d368423, d369120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38768 q selected
  have h6 (q : Pattern) (selected : d368424 q = 0) : d369121 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368424, d369121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368424, d369121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d368425 q = 0) : d369122 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d368425, d369122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d368425, d369122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d368439 q = 0) : d369136 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368439, d369136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38771 q selected
    | true =>
      simp only [d368439, d369136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38759 q selected
  have h9 (q : Pattern) (selected : d368485 q = 0) : d369087 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368485, d369087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38780 q selected
    | true =>
      simp only [d368485, d369087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38781 q selected
  have h10 (q : Pattern) (selected : d368486 q = 0) : d369137 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368486, d369137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d368486, d369137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d368507 q = 0) : d369158 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368507, d369158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38786 q selected
    | true =>
      simp only [d368507, d369158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d368508 q = 0) : d369159 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368508, d369159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d368508, d369159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d368509 q = 0) : d369160 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d368509, d369160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d368509, d369160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d368510 q = 0) : d369161 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d368510, d369161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368510, d369161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d368511 q = 0) : d369162 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d368511, d369162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368511, d369162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d368512 q = 0) : d369163 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d368512, d369163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368512, d369163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro38788 (p : Pattern) (selected : d368513 p = 0) : d369164 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368376 q = 0) : d369073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368376, d369073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38757 q selected
    | true =>
      simp only [d368376, d369073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368377 q = 0) : d369074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368377, d369074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368377, d369074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368380 q = 0) : d369077 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368380, d369077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38758 q selected
    | true =>
      simp only [d368380, d369077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368381 q = 0) : d369078 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368381, d369078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368381, d369078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d368382 q = 0) : d369079 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d368382, d369079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368382, d369079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368383 q = 0) : d369080 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d368383, d369080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368383, d369080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d368409 q = 0) : d369106 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d368409, d369106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368409, d369106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d368513 q = 0) : d369164 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d368513, d369164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368513, d369164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro38789 (p : Pattern) (selected : d368514 p = 0) : d369165 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368380 q = 0) : d369077 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368380, d369077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38758 q selected
    | true =>
      simp only [d368380, d369077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368381 q = 0) : d369078 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368381, d369078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368381, d369078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368386 q = 0) : d369083 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d368386, d369083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368386, d369083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368387 q = 0) : d369084 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d368387, d369084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368387, d369084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368411 q = 0) : d369108 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d368411, d369108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368411, d369108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368514 q = 0) : d369165 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d368514, d369165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368514, d369165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38790 (p : Pattern) (selected : d368519 p = 0) : d369170 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368376 q = 0) : d369073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368376, d369073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38757 q selected
    | true =>
      simp only [d368376, d369073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368377 q = 0) : d369074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368377, d369074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368377, d369074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368380 q = 0) : d369077 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368380, d369077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38758 q selected
    | true =>
      simp only [d368380, d369077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368381 q = 0) : d369078 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368381, d369078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368381, d369078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d368382 q = 0) : d369079 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d368382, d369079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368382, d369079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368417 q = 0) : d369114 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d368417, d369114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368417, d369114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d368418 q = 0) : d369115 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d368418, d369115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d368418, d369115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d368519 q = 0) : d369170 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d368519, d369170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368519, d369170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro38791 (p : Pattern) (selected : d368520 p = 0) : d369171 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368380 q = 0) : d369077 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368380, d369077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38758 q selected
    | true =>
      simp only [d368380, d369077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368381 q = 0) : d369078 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368381, d369078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368381, d369078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368386 q = 0) : d369083 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d368386, d369083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368386, d369083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368420 q = 0) : d369117 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d368420, d369117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368420, d369117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d368421 q = 0) : d369118 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d368421, d369118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368421, d369118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d368520 q = 0) : d369171 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d368520, d369171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368520, d369171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38792 (p : Pattern) (selected : d368524 p = 0) : d369175 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368433 q = 0) : d369130 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368433, d369130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38770 q selected
    | true =>
      simp only [d368433, d369130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368434 q = 0) : d369131 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368434, d369131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368434, d369131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368376 q = 0) : d369073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368376, d369073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38757 q selected
    | true =>
      simp only [d368376, d369073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368377 q = 0) : d369074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368377, d369074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368377, d369074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d368435 q = 0) : d369132 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d368435, d369132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368435, d369132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368436 q = 0) : d369133 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d368436, d369133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368436, d369133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d368437 q = 0) : d369134 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d368437, d369134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d368437, d369134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d368524 q = 0) : d369175 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d368524, d369175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368524, d369175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro38793 (p : Pattern) (selected : d368526 p = 0) : d369095 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368471 q = 0) : d369073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368471, d369073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38778 q selected
    | true =>
      simp only [d368471, d369073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368472 q = 0) : d369074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368472, d369074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368472, d369074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368475 q = 0) : d369077 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368475, d369077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38779 q selected
    | true =>
      simp only [d368475, d369077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368476 q = 0) : d369078 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368476, d369078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368476, d369078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d368477 q = 0) : d369079 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d368477, d369079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368477, d369079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368478 q = 0) : d369080 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d368478, d369080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368478, d369080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d368479 q = 0) : d369081 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d368479, d369081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d368479, d369081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d368526 q = 0) : d369095 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d368526, d369095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368526, d369095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro38794 (p : Pattern) (selected : d368527 p = 0) : d369096 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368475 q = 0) : d369077 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368475, d369077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38779 q selected
    | true =>
      simp only [d368475, d369077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368476 q = 0) : d369078 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368476, d369078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368476, d369078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368481 q = 0) : d369083 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d368481, d369083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368481, d369083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368482 q = 0) : d369084 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d368482, d369084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368482, d369084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368483 q = 0) : d369085 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d368483, d369085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368483, d369085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d368527 q = 0) : d369096 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d368527, d369096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368527, d369096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38795 (p : Pattern) (selected : d368530 p = 0) : d369178 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368501 q = 0) : d369152 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368501, d369152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38785 q selected
    | true =>
      simp only [d368501, d369152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368502 q = 0) : d369153 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368502, d369153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368502, d369153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368503 q = 0) : d369154 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d368503, d369154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368503, d369154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368504 q = 0) : d369155 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d368504, d369155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368504, d369155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368505 q = 0) : d369156 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d368505, d369156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368505, d369156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d368530 q = 0) : d369178 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d368530, d369178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368530, d369178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38796 (p : Pattern) (selected : d368536 p = 0) : d369184 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368413 q = 0) : d369110 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368413, d369110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38765 q selected
    | true =>
      simp only [d368413, d369110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38766 q selected
  have h2 (q : Pattern) (selected : d368414 q = 0) : d369111 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368414, d369111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368414, d369111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368415 q = 0) : d369112 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d368415, d369112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368415, d369112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368416 q = 0) : d369113 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d368416, d369113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368416, d369113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d368423 q = 0) : d369120 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368423, d369120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38767 q selected
    | true =>
      simp only [d368423, d369120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38768 q selected
  have h6 (q : Pattern) (selected : d368424 q = 0) : d369121 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368424, d369121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368424, d369121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d368425 q = 0) : d369122 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d368425, d369122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d368425, d369122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d368439 q = 0) : d369136 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368439, d369136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38771 q selected
    | true =>
      simp only [d368439, d369136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38759 q selected
  have h9 (q : Pattern) (selected : d368485 q = 0) : d369087 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368485, d369087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38780 q selected
    | true =>
      simp only [d368485, d369087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38781 q selected
  have h10 (q : Pattern) (selected : d368486 q = 0) : d369137 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368486, d369137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d368486, d369137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d368507 q = 0) : d369158 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368507, d369158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38786 q selected
    | true =>
      simp only [d368507, d369158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d368508 q = 0) : d369159 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368508, d369159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d368508, d369159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d368509 q = 0) : d369160 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d368509, d369160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d368509, d369160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d368510 q = 0) : d369161 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d368510, d369161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368510, d369161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d368511 q = 0) : d369162 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d368511, d369162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368511, d369162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d368515 q = 0) : d369166 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368515, d369166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38788 q selected
    | true =>
      simp only [d368515, d369166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38789 q selected
  have h17 (q : Pattern) (selected : d368516 q = 0) : d369167 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368516, d369167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368516, d369167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d368517 q = 0) : d369168 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d368517, d369168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d368517, d369168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d368518 q = 0) : d369169 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d368518, d369169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368518, d369169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d368521 q = 0) : d369172 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368521, d369172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38790 q selected
    | true =>
      simp only [d368521, d369172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38791 q selected
  have h21 (q : Pattern) (selected : d368522 q = 0) : d369173 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368522, d369173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368522, d369173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d368523 q = 0) : d369174 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d368523, d369174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d368523, d369174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d368525 q = 0) : d369176 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368525, d369176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38792 q selected
    | true =>
      simp only [d368525, d369176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38762 q selected
  have h24 (q : Pattern) (selected : d368528 q = 0) : d369097 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368528, d369097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38793 q selected
    | true =>
      simp only [d368528, d369097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38794 q selected
  have h25 (q : Pattern) (selected : d368529 q = 0) : d369177 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368529, d369177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d368529, d369177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d368531 q = 0) : d369179 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368531, d369179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38795 q selected
    | true =>
      simp only [d368531, d369179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d368532 q = 0) : d369180 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368532, d369180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d368532, d369180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d368533 q = 0) : d369181 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d368533, d369181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d368533, d369181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d368534 q = 0) : d369182 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d368534, d369182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d368534, d369182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d368535 q = 0) : d369183 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d368535, d369183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d368535, d369183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d368536 q = 0) : d369184 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d368536, d369184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d368536, d369184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro38797 (p : Pattern) (selected : d368543 p = 0) : d369191 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368390 q = 0) : d369087 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368390, d369087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38759 q selected
    | true =>
      simp only [d368390, d369087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38760 q selected
  have h2 (q : Pattern) (selected : d368391 q = 0) : d369088 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368391, d369088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368391, d369088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368392 q = 0) : d369089 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d368392, d369089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368392, d369089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368393 q = 0) : d369090 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d368393, d369090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368393, d369090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d368394 q = 0) : d369091 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d368394, d369091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368394, d369091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368538 q = 0) : d369186 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368538, d369186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38760 q selected
    | true =>
      simp only [d368538, d369186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d368539 q = 0) : d369187 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368539, d369187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368539, d369187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d368540 q = 0) : d369188 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d368540, d369188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368540, d369188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d368541 q = 0) : d369189 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d368541, d369189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368541, d369189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d368542 q = 0) : d369190 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d368542, d369190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368542, d369190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d368543 q = 0) : d369191 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d368543, d369191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368543, d369191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro38798 (p : Pattern) (selected : d368549 p = 0) : d369197 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368538 q = 0) : d369186 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368538, d369186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38760 q selected
    | true =>
      simp only [d368538, d369186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368539 q = 0) : d369187 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368539, d369187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368539, d369187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368540 q = 0) : d369188 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d368540, d369188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368540, d369188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368541 q = 0) : d369189 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d368541, d369189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368541, d369189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d368542 q = 0) : d369190 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d368542, d369190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368542, d369190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368544 q = 0) : d369192 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368544, d369192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38763 q selected
    | true =>
      simp only [d368544, d369192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d368545 q = 0) : d369193 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368545, d369193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368545, d369193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d368546 q = 0) : d369194 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d368546, d369194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368546, d369194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d368547 q = 0) : d369195 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d368547, d369195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368547, d369195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d368548 q = 0) : d369196 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d368548, d369196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368548, d369196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d368549 q = 0) : d369197 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d368549, d369197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368549, d369197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro38799 (p : Pattern) (selected : d368556 p = 0) : d369204 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368525 q = 0) : d369176 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368525, d369176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38792 q selected
    | true =>
      simp only [d368525, d369176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38762 q selected
  have h2 (q : Pattern) (selected : d368528 q = 0) : d369097 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368528, d369097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38793 q selected
    | true =>
      simp only [d368528, d369097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38794 q selected
  have h3 (q : Pattern) (selected : d368529 q = 0) : d369177 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368529, d369177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368529, d369177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368531 q = 0) : d369179 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368531, d369179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38795 q selected
    | true =>
      simp only [d368531, d369179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368532 q = 0) : d369180 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368532, d369180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368532, d369180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d368533 q = 0) : d369181 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d368533, d369181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368533, d369181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d368554 q = 0) : d369202 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d368554, d369202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368554, d369202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d368555 q = 0) : d369203 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d368555, d369203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368555, d369203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d368556 q = 0) : d369204 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d368556, d369204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368556, d369204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro38800 (p : Pattern) (selected : d368558 p = 0) : d369206 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368544 q = 0) : d369192 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368544, d369192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38763 q selected
    | true =>
      simp only [d368544, d369192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368545 q = 0) : d369193 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368545, d369193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368545, d369193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368546 q = 0) : d369194 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d368546, d369194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368546, d369194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368547 q = 0) : d369195 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d368547, d369195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368547, d369195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d368548 q = 0) : d369196 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d368548, d369196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368548, d369196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368558 q = 0) : d369206 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d368558, d369206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368558, d369206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro38801 (p : Pattern) (selected : d368569 p = 0) : d369217 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368564 q = 0) : d369212 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368564, d369212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368564, d369212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38752 q selected
  have h2 (q : Pattern) (selected : d368351 q = 0) : d369048 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368351, d369048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38752 q selected
    | true =>
      simp only [d368351, d369048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d368565 q = 0) : d369213 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368565, d369213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368565, d369213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368352 q = 0) : d369049 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368352, d369049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368352, d369049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368566 q = 0) : d369214 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368566, d369214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368566, d369214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368567 q = 0) : d369215 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368567, d369215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368567, d369215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d368568 q = 0) : d369216 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368568, d369216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368568, d369216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d368569 q = 0) : d369217 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d368569, d369217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368569, d369217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro38802 (p : Pattern) (selected : d368575 p = 0) : d369223 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368564 q = 0) : d369212 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368564, d369212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368564, d369212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38752 q selected
  have h2 (q : Pattern) (selected : d368351 q = 0) : d369048 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368351, d369048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38752 q selected
    | true =>
      simp only [d368351, d369048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d368565 q = 0) : d369213 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368565, d369213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368565, d369213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368352 q = 0) : d369049 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368352, d369049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368352, d369049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368566 q = 0) : d369214 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368566, d369214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368566, d369214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368567 q = 0) : d369215 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368567, d369215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368567, d369215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d368568 q = 0) : d369216 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368568, d369216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368568, d369216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d368570 q = 0) : d369218 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368570, d369218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368570, d369218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38753 q selected
  have h9 (q : Pattern) (selected : d368357 q = 0) : d369054 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368357, d369054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38753 q selected
    | true =>
      simp only [d368357, d369054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d368571 q = 0) : d369219 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368571, d369219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d368571, d369219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d368358 q = 0) : d369055 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368358, d369055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d368358, d369055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d368572 q = 0) : d369220 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368572, d369220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d368572, d369220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d368573 q = 0) : d369221 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368573, d369221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d368573, d369221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d368574 q = 0) : d369222 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368574, d369222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d368574, d369222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d368575 q = 0) : d369223 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d368575, d369223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368575, d369223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro38803 (p : Pattern) (selected : d368580 p = 0) : d369228 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368564 q = 0) : d369212 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368564, d369212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368564, d369212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38752 q selected
  have h2 (q : Pattern) (selected : d368351 q = 0) : d369048 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368351, d369048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38752 q selected
    | true =>
      simp only [d368351, d369048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d368565 q = 0) : d369213 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368565, d369213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368565, d369213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368352 q = 0) : d369049 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368352, d369049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368352, d369049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368566 q = 0) : d369214 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368566, d369214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368566, d369214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368567 q = 0) : d369215 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368567, d369215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368567, d369215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d368570 q = 0) : d369218 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368570, d369218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368570, d369218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38753 q selected
  have h8 (q : Pattern) (selected : d368357 q = 0) : d369054 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368357, d369054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38753 q selected
    | true =>
      simp only [d368357, d369054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d368571 q = 0) : d369219 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368571, d369219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368571, d369219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d368358 q = 0) : d369055 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368358, d369055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d368358, d369055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d368572 q = 0) : d369220 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368572, d369220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d368572, d369220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d368573 q = 0) : d369221 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368573, d369221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d368573, d369221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d368574 q = 0) : d369222 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368574, d369222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d368574, d369222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d368579 q = 0) : d369227 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368579, d369227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d368579, d369227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d368580 q = 0) : d369228 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d368580, d369228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d368580, d369228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro38804 (p : Pattern) (selected : d368585 p = 0) : d369233 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368570 q = 0) : d369218 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368570, d369218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368570, d369218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38753 q selected
  have h2 (q : Pattern) (selected : d368357 q = 0) : d369054 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368357, d369054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38753 q selected
    | true =>
      simp only [d368357, d369054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d368571 q = 0) : d369219 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368571, d369219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368571, d369219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368358 q = 0) : d369055 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368358, d369055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368358, d369055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368572 q = 0) : d369220 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368572, d369220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368572, d369220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368573 q = 0) : d369221 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368573, d369221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368573, d369221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d368579 q = 0) : d369227 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368579, d369227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d368579, d369227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d219016 q = 0) : d220897 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d219016, d220897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d219016, d220897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21548 q selected
  have h9 (q : Pattern) (selected : d218659 q = 0) : d220657 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d218659, d220657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21548 q selected
    | true =>
      simp only [d218659, d220657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d219017 q = 0) : d220898 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d219017, d220898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d219017, d220898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d218660 q = 0) : d220658 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d218660, d220658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d218660, d220658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d219018 q = 0) : d220899 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d219018, d220899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d219018, d220899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d219019 q = 0) : d220900 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d219019, d220900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d219019, d220900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d219020 q = 0) : d220901 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d219020, d220901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d219020, d220901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d368585 q = 0) : d369233 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d368585, d369233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368585, d369233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro38805 (p : Pattern) (selected : d368591 p = 0) : d369239 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368576 q = 0) : d369224 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d368576, d369224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38801 q selected
    | true =>
      simp only [d368576, d369224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38802 q selected
  have h2 (q : Pattern) (selected : d368577 q = 0) : d369225 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d368577, d369225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368577, d369225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368578 q = 0) : d369226 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d368578, d369226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368578, d369226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368581 q = 0) : d369229 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d368581, d369229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38802 q selected
    | true =>
      simp only [d368581, d369229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38803 q selected
  have h5 (q : Pattern) (selected : d368582 q = 0) : d369230 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d368582, d369230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368582, d369230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368583 q = 0) : d369231 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d368583, d369231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368583, d369231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d368584 q = 0) : d369232 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d368584, d369232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368584, d369232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d368586 q = 0) : d369234 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d368586, d369234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38803 q selected
    | true =>
      simp only [d368586, d369234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38804 q selected
  have h9 (q : Pattern) (selected : d368587 q = 0) : d369235 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d368587, d369235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368587, d369235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d368588 q = 0) : d369236 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d368588, d369236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368588, d369236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d368589 q = 0) : d369237 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d368589, d369237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d368589, d369237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d368590 q = 0) : d369238 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d368590, d369238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368590, d369238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d368591 q = 0) : d369239 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d368591, d369239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d368591, d369239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro38806 (p : Pattern) (selected : d368596 p = 0) : d369244 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368581 q = 0) : d369229 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d368581, d369229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38802 q selected
    | true =>
      simp only [d368581, d369229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38803 q selected
  have h2 (q : Pattern) (selected : d368582 q = 0) : d369230 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d368582, d369230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368582, d369230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368583 q = 0) : d369231 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d368583, d369231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368583, d369231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368586 q = 0) : d369234 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d368586, d369234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38803 q selected
    | true =>
      simp only [d368586, d369234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38804 q selected
  have h5 (q : Pattern) (selected : d368587 q = 0) : d369235 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d368587, d369235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368587, d369235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368588 q = 0) : d369236 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d368588, d369236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368588, d369236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d368589 q = 0) : d369237 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d368589, d369237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368589, d369237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d368594 q = 0) : d369242 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d368594, d369242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d368594, d369242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d368595 q = 0) : d369243 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d368595, d369243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368595, d369243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d368596 q = 0) : d369244 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d368596, d369244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d368596, d369244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro38807 (p : Pattern) (selected : d368602 p = 0) : d369250 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368592 q = 0) : d369240 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368592, d369240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38805 q selected
    | true =>
      simp only [d368592, d369240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368593 q = 0) : d369241 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368593, d369241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368593, d369241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368597 q = 0) : d369245 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368597, d369245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38806 q selected
    | true =>
      simp only [d368597, d369245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368598 q = 0) : d369246 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368598, d369246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368598, d369246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d368599 q = 0) : d369247 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d368599, d369247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368599, d369247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368600 q = 0) : d369248 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d368600, d369248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368600, d369248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d368601 q = 0) : d369249 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d368601, d369249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d368601, d369249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d368602 q = 0) : d369250 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d368602, d369250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368602, d369250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro38808 (p : Pattern) (selected : d368604 p = 0) : d369252 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368586 q = 0) : d369234 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d368586, d369234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38803 q selected
    | true =>
      simp only [d368586, d369234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38804 q selected
  have h2 (q : Pattern) (selected : d368587 q = 0) : d369235 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d368587, d369235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368587, d369235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368588 q = 0) : d369236 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d368588, d369236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368588, d369236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368594 q = 0) : d369242 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d368594, d369242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368594, d369242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368603 q = 0) : d369251 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d368603, d369251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368603, d369251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d368604 q = 0) : d369252 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d368604, d369252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368604, d369252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38809 (p : Pattern) (selected : d368610 p = 0) : d369258 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368597 q = 0) : d369245 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368597, d369245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38806 q selected
    | true =>
      simp only [d368597, d369245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368598 q = 0) : d369246 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368598, d369246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368598, d369246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368605 q = 0) : d369253 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368605, d369253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38808 q selected
    | true =>
      simp only [d368605, d369253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368606 q = 0) : d369254 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368606, d369254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368606, d369254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d368607 q = 0) : d369255 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d368607, d369255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368607, d369255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368608 q = 0) : d369256 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d368608, d369256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368608, d369256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d368609 q = 0) : d369257 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d368609, d369257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d368609, d369257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d368610 q = 0) : d369258 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d368610, d369258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368610, d369258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro38810 (p : Pattern) (selected : d368622 p = 0) : d369223 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368612 q = 0) : d369212 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368612, d369212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368612, d369212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38773 q selected
  have h2 (q : Pattern) (selected : d368446 q = 0) : d369048 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368446, d369048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38773 q selected
    | true =>
      simp only [d368446, d369048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d368613 q = 0) : d369213 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368613, d369213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368613, d369213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368447 q = 0) : d369049 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368447, d369049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368447, d369049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368614 q = 0) : d369214 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368614, d369214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368614, d369214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368615 q = 0) : d369215 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368615, d369215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368615, d369215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d368616 q = 0) : d369216 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368616, d369216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368616, d369216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d368617 q = 0) : d369218 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368617, d369218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368617, d369218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38774 q selected
  have h9 (q : Pattern) (selected : d368452 q = 0) : d369054 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368452, d369054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38774 q selected
    | true =>
      simp only [d368452, d369054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d368618 q = 0) : d369219 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368618, d369219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d368618, d369219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d368453 q = 0) : d369055 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368453, d369055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d368453, d369055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d368619 q = 0) : d369220 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368619, d369220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d368619, d369220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d368620 q = 0) : d369221 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368620, d369221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d368620, d369221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d368621 q = 0) : d369222 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368621, d369222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d368621, d369222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d368622 q = 0) : d369223 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d368622, d369223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368622, d369223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro38811 (p : Pattern) (selected : d368624 p = 0) : d369228 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368612 q = 0) : d369212 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368612, d369212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368612, d369212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38773 q selected
  have h2 (q : Pattern) (selected : d368446 q = 0) : d369048 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368446, d369048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38773 q selected
    | true =>
      simp only [d368446, d369048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d368613 q = 0) : d369213 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368613, d369213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368613, d369213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368447 q = 0) : d369049 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368447, d369049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368447, d369049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368614 q = 0) : d369214 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368614, d369214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368614, d369214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368615 q = 0) : d369215 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368615, d369215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368615, d369215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d368617 q = 0) : d369218 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368617, d369218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368617, d369218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38774 q selected
  have h8 (q : Pattern) (selected : d368452 q = 0) : d369054 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368452, d369054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38774 q selected
    | true =>
      simp only [d368452, d369054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d368618 q = 0) : d369219 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368618, d369219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368618, d369219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d368453 q = 0) : d369055 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368453, d369055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d368453, d369055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d368619 q = 0) : d369220 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368619, d369220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d368619, d369220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d368620 q = 0) : d369221 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368620, d369221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d368620, d369221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d368621 q = 0) : d369222 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368621, d369222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d368621, d369222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d368623 q = 0) : d369227 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368623, d369227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d368623, d369227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d368624 q = 0) : d369228 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d368624, d369228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d368624, d369228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro38812 (p : Pattern) (selected : d368628 p = 0) : d369233 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368617 q = 0) : d369218 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368617, d369218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368617, d369218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38774 q selected
  have h2 (q : Pattern) (selected : d368452 q = 0) : d369054 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368452, d369054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38774 q selected
    | true =>
      simp only [d368452, d369054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d368618 q = 0) : d369219 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368618, d369219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368618, d369219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368453 q = 0) : d369055 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368453, d369055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368453, d369055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368619 q = 0) : d369220 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368619, d369220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368619, d369220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368620 q = 0) : d369221 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368620, d369221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368620, d369221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d368623 q = 0) : d369227 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368623, d369227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d368623, d369227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d219091 q = 0) : d220897 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d219091, d220897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d219091, d220897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21586 q selected
  have h9 (q : Pattern) (selected : d218847 q = 0) : d220657 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d218847, d220657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21586 q selected
    | true =>
      simp only [d218847, d220657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d219092 q = 0) : d220898 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d219092, d220898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d219092, d220898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d218848 q = 0) : d220658 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d218848, d220658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d218848, d220658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d219093 q = 0) : d220899 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d219093, d220899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d219093, d220899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d219094 q = 0) : d220900 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d219094, d220900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d219094, d220900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d219095 q = 0) : d220901 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d219095, d220901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d219095, d220901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d368628 q = 0) : d369233 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d368628, d369233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368628, d369233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro38813 (p : Pattern) (selected : d368635 p = 0) : d369244 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368625 q = 0) : d369229 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d368625, d369229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38810 q selected
    | true =>
      simp only [d368625, d369229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38811 q selected
  have h2 (q : Pattern) (selected : d368626 q = 0) : d369230 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d368626, d369230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368626, d369230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368627 q = 0) : d369231 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d368627, d369231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368627, d369231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368629 q = 0) : d369234 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d368629, d369234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38811 q selected
    | true =>
      simp only [d368629, d369234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38812 q selected
  have h5 (q : Pattern) (selected : d368630 q = 0) : d369235 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d368630, d369235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368630, d369235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368631 q = 0) : d369236 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d368631, d369236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368631, d369236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d368632 q = 0) : d369237 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d368632, d369237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368632, d369237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d368633 q = 0) : d369242 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d368633, d369242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d368633, d369242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d368634 q = 0) : d369243 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d368634, d369243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368634, d369243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d368635 q = 0) : d369244 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d368635, d369244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d368635, d369244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro38814 (p : Pattern) (selected : d368639 p = 0) : d369252 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368629 q = 0) : d369234 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d368629, d369234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38811 q selected
    | true =>
      simp only [d368629, d369234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38812 q selected
  have h2 (q : Pattern) (selected : d368630 q = 0) : d369235 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d368630, d369235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368630, d369235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368631 q = 0) : d369236 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d368631, d369236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368631, d369236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368633 q = 0) : d369242 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d368633, d369242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368633, d369242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368638 q = 0) : d369251 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d368638, d369251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368638, d369251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d368639 q = 0) : d369252 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d368639, d369252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368639, d369252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38815 (p : Pattern) (selected : d368645 p = 0) : d369258 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368636 q = 0) : d369245 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368636, d369245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38813 q selected
    | true =>
      simp only [d368636, d369245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368637 q = 0) : d369246 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368637, d369246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368637, d369246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368640 q = 0) : d369253 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368640, d369253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38814 q selected
    | true =>
      simp only [d368640, d369253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368641 q = 0) : d369254 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368641, d369254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368641, d369254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d368642 q = 0) : d369255 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d368642, d369255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368642, d369255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368643 q = 0) : d369256 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d368643, d369256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368643, d369256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d368644 q = 0) : d369257 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d368644, d369257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d368644, d369257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d368645 q = 0) : d369258 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d368645, d369258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368645, d369258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro38816 (p : Pattern) (selected : d368648 p = 0) : d369262 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2 q = 0) : d0 q = 1 := by
    change (2 : Int) = 0 at selected
    omega
  have h2 (q : Pattern) (selected : d158 q = 0) : d127 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d158, d127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d158, d127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d35873 q = 0) : d263912 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d35873, d263912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d35873, d263912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d35874 q = 0) : d263913 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d35874, d263913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d35874, d263913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368646 q = 0) : d369260 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d368646, d369260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368646, d369260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368647 q = 0) : d369261 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d368647, d369261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368647, d369261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d368648 q = 0) : d369262 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d368648, d369262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368648, d369262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro38817 (p : Pattern) (selected : d368653 p = 0) : d369267 p = 1 := by
  have h0 (q : Pattern) (selected : d368649 q = 0) : d369263 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d368649, d369263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38816 q selected
    | true =>
      simp only [d368649, d369263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21582 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d368650 q = 0) : d369264 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d368650, d369264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368650, d369264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d218842 q = 0) : d220652 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d218842, d220652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21582 q selected
    | true =>
      simp only [d218842, d220652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d218843 q = 0) : d220653 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d218843, d220653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d218843, d220653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d368651 q = 0) : d369265 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d368651, d369265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368651, d369265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368652 q = 0) : d369266 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d368652, d369266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368652, d369266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h7 (q : Pattern) (selected : d368653 q = 0) : d369267 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d368653, d369267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d368653, d369267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h7 p selected
theorem eqIntro38818 (p : Pattern) (selected : d368659 p = 0) : d369273 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368617 q = 0) : d369218 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368617, d369218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368617, d369218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38774 q selected
  have h2 (q : Pattern) (selected : d368452 q = 0) : d369054 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368452, d369054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38774 q selected
    | true =>
      simp only [d368452, d369054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d368618 q = 0) : d369219 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368618, d369219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368618, d369219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368453 q = 0) : d369055 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368453, d369055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368453, d369055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368619 q = 0) : d369220 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368619, d369220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368619, d369220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368620 q = 0) : d369221 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368620, d369221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368620, d369221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d368623 q = 0) : d369227 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368623, d369227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d368623, d369227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d219091 q = 0) : d220897 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d219091, d220897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d219091, d220897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21586 q selected
  have h9 (q : Pattern) (selected : d218847 q = 0) : d220657 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d218847, d220657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21586 q selected
    | true =>
      simp only [d218847, d220657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d219092 q = 0) : d220898 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d219092, d220898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d219092, d220898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d368654 q = 0) : d369268 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368654, d369268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38817 q selected
    | true =>
      simp only [d368654, d369268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d368655 q = 0) : d369269 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368655, d369269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d368655, d369269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d368656 q = 0) : d369270 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368656, d369270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d368656, d369270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d368657 q = 0) : d369271 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368657, d369271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d368657, d369271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d368658 q = 0) : d369272 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368658, d369272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d368658, d369272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d368659 q = 0) : d369273 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d368659, d369273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368659, d369273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro38819 (p : Pattern) (selected : d368665 p = 0) : d369279 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368660 q = 0) : d369274 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d368660, d369274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38811 q selected
    | true =>
      simp only [d368660, d369274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38818 q selected
  have h2 (q : Pattern) (selected : d368661 q = 0) : d369275 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d368661, d369275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368661, d369275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368662 q = 0) : d369276 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d368662, d369276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368662, d369276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368663 q = 0) : d369277 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d368663, d369277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368663, d369277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368664 q = 0) : d369278 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d368664, d369278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368664, d369278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d368665 q = 0) : d369279 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d368665, d369279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368665, d369279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38820 (p : Pattern) (selected : d368671 p = 0) : d369285 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368666 q = 0) : d369280 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368666, d369280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38819 q selected
    | true =>
      simp only [d368666, d369280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368667 q = 0) : d369281 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368667, d369281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368667, d369281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368668 q = 0) : d369282 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d368668, d369282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368668, d369282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368669 q = 0) : d369283 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d368669, d369283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368669, d369283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368670 q = 0) : d369284 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d368670, d369284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368670, d369284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d368671 q = 0) : d369285 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d368671, d369285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368671, d369285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38821 (p : Pattern) (selected : d368679 p = 0) : d369293 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368564 q = 0) : d369212 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368564, d369212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368564, d369212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38752 q selected
  have h2 (q : Pattern) (selected : d368351 q = 0) : d369048 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368351, d369048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38752 q selected
    | true =>
      simp only [d368351, d369048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d368565 q = 0) : d369213 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368565, d369213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368565, d369213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368352 q = 0) : d369049 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368352, d369049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368352, d369049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368566 q = 0) : d369214 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368566, d369214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368566, d369214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368567 q = 0) : d369215 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368567, d369215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368567, d369215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d368570 q = 0) : d369218 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368570, d369218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368570, d369218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38753 q selected
  have h8 (q : Pattern) (selected : d368357 q = 0) : d369054 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368357, d369054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38753 q selected
    | true =>
      simp only [d368357, d369054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d368571 q = 0) : d369219 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368571, d369219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368571, d369219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d368358 q = 0) : d369055 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368358, d369055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d368358, d369055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d368572 q = 0) : d369220 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368572, d369220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d368572, d369220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d368573 q = 0) : d369221 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368573, d369221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d368573, d369221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d368574 q = 0) : d369222 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368574, d369222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d368574, d369222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d368674 q = 0) : d369288 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368674, d369288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368674, d369288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38782 q selected
  have h15 (q : Pattern) (selected : d368488 q = 0) : d369139 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368488, d369139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38782 q selected
    | true =>
      simp only [d368488, d369139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d368675 q = 0) : d369289 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368675, d369289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d368675, d369289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d368489 q = 0) : d369140 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368489, d369140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d368489, d369140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d368676 q = 0) : d369290 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368676, d369290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d368676, d369290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d368677 q = 0) : d369291 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368677, d369291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d368677, d369291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d368678 q = 0) : d369292 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368678, d369292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d368678, d369292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d368679 q = 0) : d369293 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d368679, d369293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d368679, d369293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro38822 (p : Pattern) (selected : d368680 p = 0) : d369294 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368674 q = 0) : d369288 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368674, d369288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368674, d369288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38782 q selected
  have h2 (q : Pattern) (selected : d368488 q = 0) : d369139 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368488, d369139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38782 q selected
    | true =>
      simp only [d368488, d369139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d368675 q = 0) : d369289 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368675, d369289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368675, d369289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368489 q = 0) : d369140 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368489, d369140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368489, d369140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368676 q = 0) : d369290 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368676, d369290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368676, d369290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368677 q = 0) : d369291 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368677, d369291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368677, d369291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d368678 q = 0) : d369292 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368678, d369292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d368678, d369292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d368680 q = 0) : d369294 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d368680, d369294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368680, d369294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro38823 (p : Pattern) (selected : d368686 p = 0) : d369300 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368581 q = 0) : d369229 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d368581, d369229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38802 q selected
    | true =>
      simp only [d368581, d369229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38803 q selected
  have h2 (q : Pattern) (selected : d368582 q = 0) : d369230 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d368582, d369230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368582, d369230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368583 q = 0) : d369231 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d368583, d369231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368583, d369231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368586 q = 0) : d369234 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d368586, d369234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38803 q selected
    | true =>
      simp only [d368586, d369234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38804 q selected
  have h5 (q : Pattern) (selected : d368587 q = 0) : d369235 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d368587, d369235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368587, d369235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368588 q = 0) : d369236 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d368588, d369236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368588, d369236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d368589 q = 0) : d369237 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d368589, d369237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368589, d369237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d368681 q = 0) : d369295 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d368681, d369295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38821 q selected
    | true =>
      simp only [d368681, d369295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38822 q selected
  have h9 (q : Pattern) (selected : d368682 q = 0) : d369296 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d368682, d369296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368682, d369296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d368683 q = 0) : d369297 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d368683, d369297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368683, d369297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d368684 q = 0) : d369298 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d368684, d369298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d368684, d369298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d368685 q = 0) : d369299 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d368685, d369299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368685, d369299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d368686 q = 0) : d369300 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d368686, d369300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d368686, d369300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro38824 (p : Pattern) (selected : d368692 p = 0) : d369306 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368687 q = 0) : d369301 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368687, d369301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38823 q selected
    | true =>
      simp only [d368687, d369301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368688 q = 0) : d369302 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368688, d369302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368688, d369302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368689 q = 0) : d369303 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d368689, d369303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368689, d369303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368690 q = 0) : d369304 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d368690, d369304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368690, d369304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368691 q = 0) : d369305 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d368691, d369305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368691, d369305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d368692 q = 0) : d369306 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d368692, d369306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368692, d369306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38825 (p : Pattern) (selected : d368698 p = 0) : d369312 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368611 q = 0) : d369259 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368611, d369259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38807 q selected
    | true =>
      simp only [d368611, d369259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38809 q selected
  have h2 (q : Pattern) (selected : d368672 q = 0) : d369286 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368672, d369286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38815 q selected
    | true =>
      simp only [d368672, d369286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38820 q selected
  have h3 (q : Pattern) (selected : d368673 q = 0) : d369287 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368673, d369287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368673, d369287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368693 q = 0) : d369307 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368693, d369307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38824 q selected
    | true =>
      simp only [d368693, d369307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368694 q = 0) : d369308 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368694, d369308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368694, d369308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d368695 q = 0) : d369309 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d368695, d369309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368695, d369309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d368696 q = 0) : d369310 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d368696, d369310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368696, d369310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d368697 q = 0) : d369311 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d368697, d369311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368697, d369311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d368698 q = 0) : d369312 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d368698, d369312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368698, d369312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro38826 (p : Pattern) (selected : d368703 p = 0) : d369317 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368605 q = 0) : d369253 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368605, d369253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38808 q selected
    | true =>
      simp only [d368605, d369253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368606 q = 0) : d369254 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368606, d369254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368606, d369254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368700 q = 0) : d369314 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d368700, d369314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368700, d369314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368701 q = 0) : d369315 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d368701, d369315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368701, d369315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368702 q = 0) : d369316 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d368702, d369316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368702, d369316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d368703 q = 0) : d369317 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d368703, d369317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368703, d369317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38827 (p : Pattern) (selected : d368709 p = 0) : d369323 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368704 q = 0) : d369318 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368704, d369318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38826 q selected
    | true =>
      simp only [d368704, d369318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368705 q = 0) : d369319 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368705, d369319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368705, d369319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368706 q = 0) : d369320 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d368706, d369320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368706, d369320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368707 q = 0) : d369321 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d368707, d369321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368707, d369321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d368708 q = 0) : d369322 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d368708, d369322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368708, d369322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368709 q = 0) : d369323 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d368709, d369323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368709, d369323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro38828 (p : Pattern) (selected : d368715 p = 0) : d369329 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368396 q = 0) : d369093 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d368396, d369093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368396, d369093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38761 q selected
  have h2 (q : Pattern) (selected : d368397 q = 0) : d369094 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d368397, d369094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368397, d369094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d368406 q = 0) : d369103 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d368406, d369103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38761 q selected
    | true =>
      simp only [d368406, d369103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38764 q selected
  have h4 (q : Pattern) (selected : d368407 q = 0) : d369104 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d368407, d369104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368407, d369104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368408 q = 0) : d369105 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d368408, d369105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368408, d369105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368537 q = 0) : d369185 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d368537, d369185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38787 q selected
    | true =>
      simp only [d368537, d369185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38796 q selected
  have h7 (q : Pattern) (selected : d368550 q = 0) : d369198 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d368550, d369198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38797 q selected
    | true =>
      simp only [d368550, d369198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38798 q selected
  have h8 (q : Pattern) (selected : d368551 q = 0) : d369199 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d368551, d369199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d368551, d369199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d368552 q = 0) : d369200 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d368552, d369200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d368552, d369200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d368553 q = 0) : d369201 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d368553, d369201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368553, d369201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d368557 q = 0) : d369205 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d368557, d369205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368557, d369205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38799 q selected
  have h12 (q : Pattern) (selected : d368559 q = 0) : d369207 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d368559, d369207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368559, d369207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38800 q selected
  have h13 (q : Pattern) (selected : d368560 q = 0) : d369208 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d368560, d369208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d368560, d369208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d368561 q = 0) : d369209 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d368561, d369209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d368561, d369209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d368562 q = 0) : d369210 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d368562, d369210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d368562, d369210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d368563 q = 0) : d369211 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d368563, d369211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d368563, d369211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d368699 q = 0) : d369313 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d368699, d369313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368699, d369313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38825 q selected
  have h18 (q : Pattern) (selected : d368710 q = 0) : d369324 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d368710, d369324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368710, d369324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38827 q selected
  have h19 (q : Pattern) (selected : d368711 q = 0) : d369325 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d368711, d369325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d368711, d369325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d368712 q = 0) : d369326 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d368712, d369326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d368712, d369326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d368713 q = 0) : d369327 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d368713, d369327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d368713, d369327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d368714 q = 0) : d369328 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d368714, d369328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d368714, d369328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d368715 q = 0) : d369329 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d368715, d369329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d368715, d369329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro38829 (p : Pattern) (selected : d368721 p = 0) : d369335 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368716 q = 0) : d369330 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d368716, d369330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368716, d369330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38828 q selected
  have h2 (q : Pattern) (selected : d368717 q = 0) : d369331 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d368717, d369331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368717, d369331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368718 q = 0) : d369332 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d368718, d369332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368718, d369332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368719 q = 0) : d369333 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d368719, d369333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368719, d369333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d368720 q = 0) : d369334 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d368720, d369334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368720, d369334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368721 q = 0) : d369335 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d368721, d369335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368721, d369335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro38830 (p : Pattern) (selected : d368727 p = 0) : d369341 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368341 q = 0) : d369038 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d368341, d369038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368341, d369038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38750 q selected
  have h2 (q : Pattern) (selected : d368342 q = 0) : d369039 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d368342, d369039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368342, d369039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368343 q = 0) : d369040 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d368343, d369040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368343, d369040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368344 q = 0) : d369041 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d368344, d369041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368344, d369041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d368722 q = 0) : d369336 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d368722, d369336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368722, d369336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38829 q selected
  have h6 (q : Pattern) (selected : d368723 q = 0) : d369337 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d368723, d369337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368723, d369337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d368724 q = 0) : d369338 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d368724, d369338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368724, d369338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d368725 q = 0) : d369339 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d368725, d369339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368725, d369339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d368726 q = 0) : d369340 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d368726, d369340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368726, d369340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d368727 q = 0) : d369341 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d368727, d369341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d368727, d369341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro38831 (p : Pattern) (selected : d368733 p = 0) : d369347 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368728 q = 0) : d369342 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d368728, d369342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38830 q selected
    | true =>
      simp only [d368728, d369342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368729 q = 0) : d369343 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d368729, d369343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368729, d369343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d368730 q = 0) : d369344 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d368730, d369344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368730, d369344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368731 q = 0) : d369345 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d368731, d369345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368731, d369345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368732 q = 0) : d369346 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d368732, d369346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368732, d369346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d368733 q = 0) : d369347 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d368733, d369347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368733, d369347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38832 (p : Pattern) (selected : d368739 p = 0) : d369353 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368734 q = 0) : d369348 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d368734, d369348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38831 q selected
    | true =>
      simp only [d368734, d369348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368735 q = 0) : d369349 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d368735, d369349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368735, d369349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d368736 q = 0) : d369350 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d368736, d369350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368736, d369350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368737 q = 0) : d369351 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d368737, d369351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368737, d369351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368738 q = 0) : d369352 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d368738, d369352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368738, d369352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d368739 q = 0) : d369353 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d368739, d369353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368739, d369353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38833 (p : Pattern) (selected : d368745 p = 0) : d369359 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368740 q = 0) : d369354 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d368740, d369354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38832 q selected
    | true =>
      simp only [d368740, d369354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368741 q = 0) : d369355 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d368741, d369355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368741, d369355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d368742 q = 0) : d369356 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d368742, d369356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368742, d369356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368743 q = 0) : d369357 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d368743, d369357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368743, d369357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368744 q = 0) : d369358 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d368744, d369358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368744, d369358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d368745 q = 0) : d369359 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d368745, d369359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368745, d369359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38834 (p : Pattern) (selected : d368751 p = 0) : d369365 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368746 q = 0) : d369360 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d368746, d369360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38833 q selected
    | true =>
      simp only [d368746, d369360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368747 q = 0) : d369361 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d368747, d369361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368747, d369361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d368748 q = 0) : d369362 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d368748, d369362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368748, d369362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368749 q = 0) : d369363 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d368749, d369363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368749, d369363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368750 q = 0) : d369364 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d368750, d369364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368750, d369364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d368751 q = 0) : d369365 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d368751, d369365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368751, d369365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38835 (p : Pattern) (selected : d368757 p = 0) : d369371 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368752 q = 0) : d369366 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d368752, d369366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38834 q selected
    | true =>
      simp only [d368752, d369366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368753 q = 0) : d369367 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d368753, d369367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368753, d369367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d368754 q = 0) : d369368 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d368754, d369368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368754, d369368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368755 q = 0) : d369369 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d368755, d369369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368755, d369369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368756 q = 0) : d369370 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d368756, d369370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368756, d369370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d368757 q = 0) : d369371 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d368757, d369371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368757, d369371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38836 (p : Pattern) (selected : d368763 p = 0) : d369377 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368758 q = 0) : d369372 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d368758, d369372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38835 q selected
    | true =>
      simp only [d368758, d369372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368759 q = 0) : d369373 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d368759, d369373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368759, d369373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d368760 q = 0) : d369374 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d368760, d369374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368760, d369374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368761 q = 0) : d369375 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d368761, d369375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368761, d369375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368762 q = 0) : d369376 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d368762, d369376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368762, d369376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d368763 q = 0) : d369377 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d368763, d369377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368763, d369377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38837 (p : Pattern) (selected : d368769 p = 0) : d369383 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d368764 q = 0) : d369378 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d368764, d369378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38836 q selected
    | true =>
      simp only [d368764, d369378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368765 q = 0) : d369379 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d368765, d369379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368765, d369379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d368766 q = 0) : d369380 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d368766, d369380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368766, d369380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368767 q = 0) : d369381 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d368767, d369381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368767, d369381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368768 q = 0) : d369382 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d368768, d369382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368768, d369382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d368769 q = 0) : d369383 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d368769, d369383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368769, d369383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38838 (p : Pattern) (selected : d368081 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2 q = 1) : d0 q = 1 := by
    change (2 : Int) = 1 at selected
    omega
  have h2 (q : Pattern) (selected : d158 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d159 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1233 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d218177 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d218177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d218177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d368081 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d368081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38839 (p : Pattern) (selected : d368086 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d368082 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d368082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38838 q selected
  have h2 (q : Pattern) (selected : d368083 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d368083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d368084 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d368084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368085 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d368085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368086 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d368086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro38840 (p : Pattern) (selected : d368092 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d368082 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d368082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38838 q selected
  have h2 (q : Pattern) (selected : d368083 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d368083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d368084 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d368084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368085 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d368085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d218248 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d218248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21647 q selected
  have h6 (q : Pattern) (selected : d218249 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d218249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d218249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d216868 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d216868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21647 q selected
    | true =>
      simp only [d216868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d216869 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d216869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d216869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d218250 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d218250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d218250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d218251 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d218251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d218251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d368092 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d368092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro38841 (p : Pattern) (selected : d368098 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d368087 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38839 q selected
    | true =>
      simp only [d368087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368088 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d368089 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368090 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368091 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368093 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38840 q selected
    | true =>
      simp only [d368093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d368094 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d368094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d368095 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d368096 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d368096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d368097 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d368098 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d368098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro38842 (p : Pattern) (selected : d368100 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d368087 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38839 q selected
    | true =>
      simp only [d368087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368088 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d368089 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368090 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368093 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38840 q selected
    | true =>
      simp only [d368093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d368094 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d368095 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d368096 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d368097 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d368099 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d368099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d368100 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d368100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d368100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro38843 (p : Pattern) (selected : d368104 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d368093 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38840 q selected
    | true =>
      simp only [d368093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368094 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d368095 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368096 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368099 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d218253 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d218253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21746 q selected
    | true =>
      simp only [d218253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d218254 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d218254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d218254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d218255 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d218255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d218256 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d218256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d218256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d218257 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d218257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d218257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d368104 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d368104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro38844 (p : Pattern) (selected : d368111 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d368101 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d368101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38841 q selected
    | true =>
      simp only [d368101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38842 q selected
  have h2 (q : Pattern) (selected : d368102 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d368102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368103 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d368103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368105 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d368105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38842 q selected
    | true =>
      simp only [d368105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38843 q selected
  have h5 (q : Pattern) (selected : d368106 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d368106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368107 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d368107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d368108 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d368108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d368109 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d368109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d368109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d368110 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d368110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d368111 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d368111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d368111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro38845 (p : Pattern) (selected : d368115 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d368105 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d368105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38842 q selected
    | true =>
      simp only [d368105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38843 q selected
  have h2 (q : Pattern) (selected : d368106 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d368106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368107 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d368107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368109 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d368109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368114 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d368114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d368115 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d368115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38846 (p : Pattern) (selected : d368121 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d368112 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38844 q selected
    | true =>
      simp only [d368112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368113 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368116 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38845 q selected
    | true =>
      simp only [d368116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368117 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d368118 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d368118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368119 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d368119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d368120 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d368120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d368120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d368121 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d368121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro38847 (p : Pattern) (selected : d368125 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d368116 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38845 q selected
    | true =>
      simp only [d368116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368117 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368122 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d368122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368123 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d368123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368124 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d368124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d368125 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d368125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro38848 (p : Pattern) (selected : d368153 p = 1) : d370675 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d368057 q = 1) : d368057 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d368066 q = 1) : d368066 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d368080 q = 1) : d368080 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d368126 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38846 q selected
    | true =>
      simp only [d368126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38847 q selected
  have h5 (q : Pattern) (selected : d368127 q = 1) : d370671 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368127, d370671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368127, d370671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368149 q = 1) : d368149 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d368150 q = 1) : d370672 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d368150, d370672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368150, d370672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d368151 q = 1) : d370673 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d368151, d370673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368151, d370673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d368152 q = 1) : d370674 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d368152, d370674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368152, d370674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d368153 q = 1) : d370675 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d368153, d370675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368153, d370675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro38849 (p : Pattern) (selected : d368167 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d368112 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38844 q selected
    | true =>
      simp only [d368112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368113 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368116 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38845 q selected
    | true =>
      simp only [d368116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368117 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d368118 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d368118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368119 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d368119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d368120 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d368120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d368120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d368167 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d368167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro38850 (p : Pattern) (selected : d368168 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d368116 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38845 q selected
    | true =>
      simp only [d368116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368117 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368122 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d368122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368123 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d368123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368124 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d368124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d368168 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d368168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38851 (p : Pattern) (selected : d368177 p = 1) : d370680 p = 1 := by
  have h0 (q : Pattern) (selected : d368057 q = 1) : d368057 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d368066 q = 1) : d368066 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d368080 q = 1) : d368080 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d368126 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38846 q selected
    | true =>
      simp only [d368126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38847 q selected
  have h4 (q : Pattern) (selected : d368127 q = 1) : d370671 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368127, d370671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368127, d370671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d368149 q = 1) : d368149 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d368150 q = 1) : d370672 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d368150, d370672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368150, d370672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d368151 q = 1) : d370673 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d368151, d370673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368151, d370673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d368152 q = 1) : d370674 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d368152, d370674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368152, d370674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d368159 q = 1) : d368159 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d368164 q = 1) : d368164 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d368166 q = 1) : d368166 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d368169 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38849 q selected
    | true =>
      simp only [d368169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38850 q selected
  have h13 (q : Pattern) (selected : d368170 q = 1) : d370676 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368170, d370676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d368170, d370676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d368173 q = 1) : d368173 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d368174 q = 1) : d370677 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d368174, d370677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d368174, d370677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d368175 q = 1) : d370678 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d368175, d370678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d368175, d370678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d368176 q = 1) : d370679 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d368176, d370679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d368176, d370679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d368177 q = 1) : d370680 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d368177, d370680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d368177, d370680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro38852 (p : Pattern) (selected : d368197 p = 1) : d370687 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d368166 q = 1) : d368166 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d368169 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38849 q selected
    | true =>
      simp only [d368169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38850 q selected
  have h3 (q : Pattern) (selected : d368170 q = 1) : d370676 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368170, d370676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368170, d370676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368173 q = 1) : d368173 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d368174 q = 1) : d370677 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d368174, d370677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368174, d370677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368195 q = 1) : d370685 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d368195, d370685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368195, d370685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d368196 q = 1) : d370686 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d368196, d370686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368196, d370686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d368197 q = 1) : d370687 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d368197, d370687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368197, d370687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro38853 (p : Pattern) (selected : d368263 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d368253 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38839 q selected
  have h2 (q : Pattern) (selected : d368087 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38839 q selected
    | true =>
      simp only [d368087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d368254 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368088 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368255 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368256 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d368257 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d368258 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38840 q selected
  have h9 (q : Pattern) (selected : d368093 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38840 q selected
    | true =>
      simp only [d368093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d368259 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d368259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d368094 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d368094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d368260 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d368260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d368261 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d368261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d368262 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d368262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d368263 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d368263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro38854 (p : Pattern) (selected : d368265 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d368253 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38839 q selected
  have h2 (q : Pattern) (selected : d368087 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38839 q selected
    | true =>
      simp only [d368087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d368254 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368088 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368255 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368256 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d368258 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38840 q selected
  have h8 (q : Pattern) (selected : d368093 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38840 q selected
    | true =>
      simp only [d368093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d368259 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d368094 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d368094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d368260 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d368260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d368261 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d368261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d368262 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d368262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d368264 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d368264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d368265 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d368265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d368265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro38855 (p : Pattern) (selected : d368269 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d368258 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38840 q selected
  have h2 (q : Pattern) (selected : d368093 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38840 q selected
    | true =>
      simp only [d368093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d368259 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368094 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368260 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368261 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d368264 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d368264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d218501 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d218501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21746 q selected
  have h9 (q : Pattern) (selected : d218253 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d218253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21746 q selected
    | true =>
      simp only [d218253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d218502 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d218502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d218502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d218254 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d218254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d218254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d218503 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d218503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d218503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d218504 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d218504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d218504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d218505 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d218505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d218505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d368269 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d368269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro38856 (p : Pattern) (selected : d368276 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d368266 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d368266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38853 q selected
    | true =>
      simp only [d368266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38854 q selected
  have h2 (q : Pattern) (selected : d368267 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d368267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368268 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d368268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368270 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d368270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38854 q selected
    | true =>
      simp only [d368270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38855 q selected
  have h5 (q : Pattern) (selected : d368271 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d368271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368272 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d368272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d368273 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d368273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d368274 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d368274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d368274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d368275 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d368275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d368276 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d368276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d368276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro38857 (p : Pattern) (selected : d368280 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d368270 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d368270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38854 q selected
    | true =>
      simp only [d368270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38855 q selected
  have h2 (q : Pattern) (selected : d368271 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d368271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368272 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d368272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368274 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d368274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368279 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d368279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d368280 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d368280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38858 (p : Pattern) (selected : d368286 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d368277 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38856 q selected
    | true =>
      simp only [d368277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368278 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368281 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38857 q selected
    | true =>
      simp only [d368281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368282 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d368283 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d368283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368284 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d368284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d368285 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d368285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d368285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d368286 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d368286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro38859 (p : Pattern) (selected : d368290 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d368281 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38857 q selected
    | true =>
      simp only [d368281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368282 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368287 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d368287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368288 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d368288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368289 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d368289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d368290 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d368290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38860 (p : Pattern) (selected : d368317 p = 1) : d370697 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d368252 q = 1) : d368252 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d368291 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38858 q selected
    | true =>
      simp only [d368291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38859 q selected
  have h3 (q : Pattern) (selected : d368292 q = 1) : d370693 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368292, d370693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368292, d370693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368313 q = 1) : d368313 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d368314 q = 1) : d370694 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d368314, d370694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368314, d370694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368315 q = 1) : d370695 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d368315, d370695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368315, d370695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d368316 q = 1) : d370696 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d368316, d370696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368316, d370696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d368317 q = 1) : d370697 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d368317, d370697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368317, d370697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro38861 (p : Pattern) (selected : d368334 p = 1) : d370703 p = 1 := by
  have h0 (q : Pattern) (selected : d368049 q = 1) : d368049 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d368178 q = 1) : d370681 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d368178, d370681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38848 q selected
    | true =>
      simp only [d368178, d370681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38851 q selected
  have h2 (q : Pattern) (selected : d368191 q = 1) : d368191 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d368192 q = 1) : d370682 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d368192, d370682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368192, d370682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d368193 q = 1) : d370683 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d368193, d370683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368193, d370683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368194 q = 1) : d370684 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d368194, d370684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368194, d370684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d368198 q = 1) : d370688 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d368198, d370688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368198, d370688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38852 q selected
  have h8 (q : Pattern) (selected : d368200 q = 1) : d368200 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d368201 q = 1) : d370689 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d368201, d370689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368201, d370689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d368202 q = 1) : d370690 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d368202, d370690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d368202, d370690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d368203 q = 1) : d370691 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d368203, d370691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d368203, d370691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d368204 q = 1) : d370692 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d368204, d370692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d368204, d370692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d368318 q = 1) : d370698 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d368318, d370698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368318, d370698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38860 q selected
  have h14 (q : Pattern) (selected : d368329 q = 1) : d368329 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d368330 q = 1) : d370699 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d368330, d370699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d368330, d370699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d368331 q = 1) : d370700 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d368331, d370700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d368331, d370700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d368332 q = 1) : d370701 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d368332, d370701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d368332, d370701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d368333 q = 1) : d370702 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d368333, d370702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d368333, d370702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d368334 q = 1) : d370703 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d368334, d370703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d368334, d370703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro38862 (p : Pattern) (selected : d368340 p = 1) : d370709 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d368335 q = 1) : d370704 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d368335, d370704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368335, d370704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38861 q selected
  have h2 (q : Pattern) (selected : d368336 q = 1) : d370705 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d368336, d370705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368336, d370705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368337 q = 1) : d370706 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d368337, d370706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368337, d370706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368338 q = 1) : d370707 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d368338, d370707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368338, d370707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d368339 q = 1) : d370708 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d368339, d370708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368339, d370708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368340 q = 1) : d370709 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d368340, d370709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368340, d370709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro38863 (p : Pattern) (selected : d368440 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2 q = 1) : d0 q = 1 := by
    change (2 : Int) = 1 at selected
    omega
  have h2 (q : Pattern) (selected : d338 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d563 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1691 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d218775 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d218775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d218775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d368440 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d368440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38864 (p : Pattern) (selected : d368445 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d368441 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d368441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38863 q selected
  have h2 (q : Pattern) (selected : d368442 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d368442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d368443 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d368443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368444 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d368444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368445 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d368445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro38865 (p : Pattern) (selected : d368451 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d368441 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d368441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38863 q selected
  have h2 (q : Pattern) (selected : d368442 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d368442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d368443 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d368443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368444 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d368444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d218840 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d218840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21780 q selected
  have h6 (q : Pattern) (selected : d218841 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d218841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d218841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d218842 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d218842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21780 q selected
    | true =>
      simp only [d218842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d218843 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d218843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d218843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d218844 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d218844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d218844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d218845 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d218845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d218845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d368451 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d368451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro38866 (p : Pattern) (selected : d368457 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d368446 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38864 q selected
    | true =>
      simp only [d368446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368447 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d368448 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368449 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368450 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368452 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38865 q selected
    | true =>
      simp only [d368452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d368453 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d368453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d368454 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d368455 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d368455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d368456 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d368457 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d368457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro38867 (p : Pattern) (selected : d368459 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d368446 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38864 q selected
    | true =>
      simp only [d368446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368447 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d368448 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368449 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368452 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38865 q selected
    | true =>
      simp only [d368452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d368453 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d368454 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d368455 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d368456 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d368458 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d368458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d368459 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d368459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d368459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro38868 (p : Pattern) (selected : d368463 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d368452 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38865 q selected
    | true =>
      simp only [d368452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368453 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d368454 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368455 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368458 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d218847 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d218847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21784 q selected
    | true =>
      simp only [d218847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d218848 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d218848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d218848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d218849 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d218849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d218849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d218850 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d218850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d218850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d218851 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d218851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d218851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d368463 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d368463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro38869 (p : Pattern) (selected : d368470 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d368460 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d368460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38866 q selected
    | true =>
      simp only [d368460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38867 q selected
  have h2 (q : Pattern) (selected : d368461 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d368461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368462 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d368462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368464 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d368464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38867 q selected
    | true =>
      simp only [d368464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38868 q selected
  have h5 (q : Pattern) (selected : d368465 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d368465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368466 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d368466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d368467 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d368467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d368468 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d368468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d368468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d368469 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d368469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d368470 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d368470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d368470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro38870 (p : Pattern) (selected : d368474 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d368464 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d368464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38867 q selected
    | true =>
      simp only [d368464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38868 q selected
  have h2 (q : Pattern) (selected : d368465 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d368465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368466 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d368466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368468 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d368468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368473 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d368473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d368474 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d368474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38871 (p : Pattern) (selected : d368480 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d368471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38869 q selected
    | true =>
      simp only [d368471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368475 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38870 q selected
    | true =>
      simp only [d368475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368476 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d368477 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d368477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368478 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d368478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d368479 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d368479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d368479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d368480 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d368480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro38872 (p : Pattern) (selected : d368484 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d368475 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38870 q selected
    | true =>
      simp only [d368475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368476 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368481 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d368481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368482 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d368482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368483 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d368483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d368484 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d368484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro38873 (p : Pattern) (selected : d368512 p = 1) : d370718 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d368416 q = 1) : d368416 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d368425 q = 1) : d368425 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d368439 q = 1) : d368439 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d368485 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38871 q selected
    | true =>
      simp only [d368485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38872 q selected
  have h5 (q : Pattern) (selected : d368486 q = 1) : d370714 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368486, d370714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368486, d370714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368508 q = 1) : d368508 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d368509 q = 1) : d370715 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d368509, d370715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368509, d370715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d368510 q = 1) : d370716 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d368510, d370716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368510, d370716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d368511 q = 1) : d370717 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d368511, d370717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368511, d370717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d368512 q = 1) : d370718 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d368512, d370718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368512, d370718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro38874 (p : Pattern) (selected : d368526 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d368471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38869 q selected
    | true =>
      simp only [d368471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368475 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38870 q selected
    | true =>
      simp only [d368475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368476 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d368477 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d368477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368478 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d368478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d368479 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d368479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d368479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d368526 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d368526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro38875 (p : Pattern) (selected : d368527 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d368475 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38870 q selected
    | true =>
      simp only [d368475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368476 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368481 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d368481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368482 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d368482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368483 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d368483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d368527 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d368527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38876 (p : Pattern) (selected : d368536 p = 1) : d370723 p = 1 := by
  have h0 (q : Pattern) (selected : d368416 q = 1) : d368416 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d368425 q = 1) : d368425 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d368439 q = 1) : d368439 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d368485 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38871 q selected
    | true =>
      simp only [d368485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38872 q selected
  have h4 (q : Pattern) (selected : d368486 q = 1) : d370714 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368486, d370714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368486, d370714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d368508 q = 1) : d368508 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d368509 q = 1) : d370715 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d368509, d370715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368509, d370715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d368510 q = 1) : d370716 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d368510, d370716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368510, d370716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d368511 q = 1) : d370717 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d368511, d370717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368511, d370717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d368518 q = 1) : d368518 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d368523 q = 1) : d368523 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d368525 q = 1) : d368525 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d368528 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38874 q selected
    | true =>
      simp only [d368528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38875 q selected
  have h13 (q : Pattern) (selected : d368529 q = 1) : d370719 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368529, d370719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d368529, d370719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d368532 q = 1) : d368532 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d368533 q = 1) : d370720 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d368533, d370720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d368533, d370720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d368534 q = 1) : d370721 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d368534, d370721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d368534, d370721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d368535 q = 1) : d370722 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d368535, d370722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d368535, d370722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d368536 q = 1) : d370723 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d368536, d370723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d368536, d370723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro38877 (p : Pattern) (selected : d368556 p = 1) : d370730 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d368525 q = 1) : d368525 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d368528 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38874 q selected
    | true =>
      simp only [d368528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38875 q selected
  have h3 (q : Pattern) (selected : d368529 q = 1) : d370719 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368529, d370719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368529, d370719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368532 q = 1) : d368532 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d368533 q = 1) : d370720 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d368533, d370720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368533, d370720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368554 q = 1) : d370728 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d368554, d370728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368554, d370728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d368555 q = 1) : d370729 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d368555, d370729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368555, d370729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d368556 q = 1) : d370730 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d368556, d370730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368556, d370730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro38878 (p : Pattern) (selected : d368622 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d368612 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38864 q selected
  have h2 (q : Pattern) (selected : d368446 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38864 q selected
    | true =>
      simp only [d368446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d368613 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368447 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368614 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368615 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d368616 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d368617 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38865 q selected
  have h9 (q : Pattern) (selected : d368452 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38865 q selected
    | true =>
      simp only [d368452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d368618 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d368618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d368453 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d368453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d368619 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d368619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d368620 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d368620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d368621 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d368621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d368622 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d368622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro38879 (p : Pattern) (selected : d368624 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d368612 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38864 q selected
  have h2 (q : Pattern) (selected : d368446 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38864 q selected
    | true =>
      simp only [d368446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d368613 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368447 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368614 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368615 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d368617 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38865 q selected
  have h8 (q : Pattern) (selected : d368452 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38865 q selected
    | true =>
      simp only [d368452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d368618 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d368453 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d368453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d368619 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d368619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d368620 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d368620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d368621 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d368621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d368623 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d368623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d368624 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d368624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d368624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro38880 (p : Pattern) (selected : d368628 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d368617 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38865 q selected
  have h2 (q : Pattern) (selected : d368452 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38865 q selected
    | true =>
      simp only [d368452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d368618 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368453 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368619 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368620 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d368623 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d368623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d219091 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d219091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d219091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21784 q selected
  have h9 (q : Pattern) (selected : d218847 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d218847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21784 q selected
    | true =>
      simp only [d218847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d219092 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d219092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d219092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d218848 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d218848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d218848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d219093 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d219093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d219093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d219094 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d219094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d219094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d219095 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d219095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d219095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d368628 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d368628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro38881 (p : Pattern) (selected : d368635 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d368625 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d368625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38878 q selected
    | true =>
      simp only [d368625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38879 q selected
  have h2 (q : Pattern) (selected : d368626 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d368626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368627 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d368627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368629 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d368629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38879 q selected
    | true =>
      simp only [d368629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38880 q selected
  have h5 (q : Pattern) (selected : d368630 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d368630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368631 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d368631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d368632 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d368632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d368633 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d368633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d368633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d368634 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d368634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d368635 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d368635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d368635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro38882 (p : Pattern) (selected : d368639 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d368629 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d368629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38879 q selected
    | true =>
      simp only [d368629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38880 q selected
  have h2 (q : Pattern) (selected : d368630 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d368630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368631 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d368631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368633 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d368633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368638 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d368638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d368639 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d368639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38883 (p : Pattern) (selected : d368645 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d368636 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38881 q selected
    | true =>
      simp only [d368636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368637 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368640 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38882 q selected
    | true =>
      simp only [d368640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368641 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d368642 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d368642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368643 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d368643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d368644 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d368644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d368644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d368645 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d368645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro38884 (p : Pattern) (selected : d368648 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2 q = 1) : d0 q = 1 := by
    change (2 : Int) = 1 at selected
    omega
  have h2 (q : Pattern) (selected : d158 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d35873 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d35873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d35873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d35874 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d35874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d35874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368646 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d368646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368647 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d368647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d368648 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d368648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro38885 (p : Pattern) (selected : d368653 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d368649 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d368649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38884 q selected
    | true =>
      simp only [d368649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21780 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d368650 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d368650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d218842 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d218842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21780 q selected
    | true =>
      simp only [d218842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d218843 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d218843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d218843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d368651 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d368651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368652 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d368652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h7 (q : Pattern) (selected : d368653 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d368653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d368653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h7 p selected
theorem eqIntro38886 (p : Pattern) (selected : d368659 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d368617 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38865 q selected
  have h2 (q : Pattern) (selected : d368452 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38865 q selected
    | true =>
      simp only [d368452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d368618 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368453 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368619 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368620 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d368623 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d368623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d219091 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d219091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d219091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21784 q selected
  have h9 (q : Pattern) (selected : d218847 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d218847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21784 q selected
    | true =>
      simp only [d218847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d219092 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d219092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d219092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d368654 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38885 q selected
    | true =>
      simp only [d368654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d368655 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d368655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d368656 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d368656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d368657 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d368657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d368658 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d368658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d368659 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d368659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro38887 (p : Pattern) (selected : d368665 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d368660 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d368660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38879 q selected
    | true =>
      simp only [d368660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38886 q selected
  have h2 (q : Pattern) (selected : d368661 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d368661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368662 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d368662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368663 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d368663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368664 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d368664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d368665 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d368665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38888 (p : Pattern) (selected : d368671 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d368666 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38887 q selected
    | true =>
      simp only [d368666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368667 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368668 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d368668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368669 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d368669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368670 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d368670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d368671 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d368671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38889 (p : Pattern) (selected : d368698 p = 1) : d370740 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d368611 q = 1) : d368611 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d368672 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38883 q selected
    | true =>
      simp only [d368672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38888 q selected
  have h3 (q : Pattern) (selected : d368673 q = 1) : d370736 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368673, d370736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368673, d370736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368694 q = 1) : d368694 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d368695 q = 1) : d370737 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d368695, d370737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368695, d370737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368696 q = 1) : d370738 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d368696, d370738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368696, d370738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d368697 q = 1) : d370739 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d368697, d370739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368697, d370739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d368698 q = 1) : d370740 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d368698, d370740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368698, d370740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro38890 (p : Pattern) (selected : d368715 p = 1) : d370746 p = 1 := by
  have h0 (q : Pattern) (selected : d368408 q = 1) : d368408 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d368537 q = 1) : d370724 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d368537, d370724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38873 q selected
    | true =>
      simp only [d368537, d370724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38876 q selected
  have h2 (q : Pattern) (selected : d368550 q = 1) : d368550 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d368551 q = 1) : d370725 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d368551, d370725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368551, d370725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d368552 q = 1) : d370726 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d368552, d370726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368552, d370726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368553 q = 1) : d370727 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d368553, d370727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368553, d370727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d368557 q = 1) : d370731 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d368557, d370731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368557, d370731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38877 q selected
  have h8 (q : Pattern) (selected : d368559 q = 1) : d368559 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d368560 q = 1) : d370732 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d368560, d370732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d368560, d370732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d368561 q = 1) : d370733 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d368561, d370733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d368561, d370733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d368562 q = 1) : d370734 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d368562, d370734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d368562, d370734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d368563 q = 1) : d370735 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d368563, d370735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d368563, d370735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d368699 q = 1) : d370741 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d368699, d370741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368699, d370741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38889 q selected
  have h14 (q : Pattern) (selected : d368710 q = 1) : d368710 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d368711 q = 1) : d370742 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d368711, d370742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d368711, d370742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d368712 q = 1) : d370743 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d368712, d370743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d368712, d370743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d368713 q = 1) : d370744 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d368713, d370744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d368713, d370744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d368714 q = 1) : d370745 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d368714, d370745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d368714, d370745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d368715 q = 1) : d370746 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d368715, d370746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d368715, d370746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro38891 (p : Pattern) (selected : d368721 p = 1) : d370752 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d368716 q = 1) : d370747 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d368716, d370747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368716, d370747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38890 q selected
  have h2 (q : Pattern) (selected : d368717 q = 1) : d370748 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d368717, d370748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368717, d370748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368718 q = 1) : d370749 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d368718, d370749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368718, d370749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368719 q = 1) : d370750 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d368719, d370750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368719, d370750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d368720 q = 1) : d370751 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d368720, d370751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368720, d370751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d368721 q = 1) : d370752 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d368721, d370752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368721, d370752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro38892 (p : Pattern) (selected : d368727 p = 1) : d370758 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d368341 q = 1) : d370710 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d368341, d370710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368341, d370710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38862 q selected
  have h2 (q : Pattern) (selected : d368342 q = 1) : d370711 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d368342, d370711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368342, d370711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d368343 q = 1) : d370712 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d368343, d370712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368343, d370712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d368344 q = 1) : d370713 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d368344, d370713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368344, d370713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d368722 q = 1) : d370753 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d368722, d370753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368722, d370753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38891 q selected
  have h6 (q : Pattern) (selected : d368723 q = 1) : d370754 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d368723, d370754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368723, d370754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d368724 q = 1) : d370755 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d368724, d370755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368724, d370755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d368725 q = 1) : d370756 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d368725, d370756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d368725, d370756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d368726 q = 1) : d370757 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d368726, d370757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368726, d370757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d368727 q = 1) : d370758 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d368727, d370758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d368727, d370758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro38893 (p : Pattern) (selected : d368733 p = 1) : d370764 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d368728 q = 1) : d370759 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d368728, d370759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38892 q selected
    | true =>
      simp only [d368728, d370759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368729 q = 1) : d370760 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d368729, d370760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368729, d370760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d368730 q = 1) : d370761 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d368730, d370761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368730, d370761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368731 q = 1) : d370762 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d368731, d370762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368731, d370762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368732 q = 1) : d370763 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d368732, d370763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368732, d370763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d368733 q = 1) : d370764 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d368733, d370764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368733, d370764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38894 (p : Pattern) (selected : d368739 p = 1) : d370770 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d368734 q = 1) : d370765 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d368734, d370765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38893 q selected
    | true =>
      simp only [d368734, d370765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368735 q = 1) : d370766 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d368735, d370766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368735, d370766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d368736 q = 1) : d370767 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d368736, d370767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368736, d370767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368737 q = 1) : d370768 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d368737, d370768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368737, d370768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368738 q = 1) : d370769 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d368738, d370769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368738, d370769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d368739 q = 1) : d370770 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d368739, d370770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368739, d370770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38895 (p : Pattern) (selected : d368745 p = 1) : d370776 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d368740 q = 1) : d370771 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d368740, d370771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38894 q selected
    | true =>
      simp only [d368740, d370771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368741 q = 1) : d370772 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d368741, d370772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368741, d370772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d368742 q = 1) : d370773 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d368742, d370773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368742, d370773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368743 q = 1) : d370774 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d368743, d370774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368743, d370774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368744 q = 1) : d370775 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d368744, d370775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368744, d370775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d368745 q = 1) : d370776 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d368745, d370776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368745, d370776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38896 (p : Pattern) (selected : d368751 p = 1) : d370782 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d368746 q = 1) : d370777 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d368746, d370777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38895 q selected
    | true =>
      simp only [d368746, d370777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368747 q = 1) : d370778 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d368747, d370778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368747, d370778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d368748 q = 1) : d370779 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d368748, d370779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368748, d370779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368749 q = 1) : d370780 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d368749, d370780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368749, d370780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368750 q = 1) : d370781 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d368750, d370781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368750, d370781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d368751 q = 1) : d370782 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d368751, d370782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368751, d370782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38897 (p : Pattern) (selected : d368757 p = 1) : d370788 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d368752 q = 1) : d370783 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d368752, d370783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38896 q selected
    | true =>
      simp only [d368752, d370783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368753 q = 1) : d370784 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d368753, d370784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368753, d370784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d368754 q = 1) : d370785 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d368754, d370785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368754, d370785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368755 q = 1) : d370786 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d368755, d370786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368755, d370786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368756 q = 1) : d370787 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d368756, d370787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368756, d370787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d368757 q = 1) : d370788 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d368757, d370788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368757, d370788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38898 (p : Pattern) (selected : d368763 p = 1) : d370794 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d368758 q = 1) : d370789 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d368758, d370789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38897 q selected
    | true =>
      simp only [d368758, d370789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368759 q = 1) : d370790 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d368759, d370790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368759, d370790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d368760 q = 1) : d370791 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d368760, d370791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368760, d370791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368761 q = 1) : d370792 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d368761, d370792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368761, d370792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368762 q = 1) : d370793 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d368762, d370793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368762, d370793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d368763 q = 1) : d370794 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d368763, d370794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368763, d370794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38899 (p : Pattern) (selected : d368769 p = 1) : d370800 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d368764 q = 1) : d370795 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d368764, d370795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38898 q selected
    | true =>
      simp only [d368764, d370795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d368765 q = 1) : d370796 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d368765, d370796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d368765, d370796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d368766 q = 1) : d370797 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d368766, d370797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d368766, d370797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d368767 q = 1) : d370798 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d368767, d370798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d368767, d370798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d368768 q = 1) : d370799 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d368768, d370799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d368768, d370799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d368769 q = 1) : d370800 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d368769, d370800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d368769, d370800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38900 (p : Pattern) (selected : d370808 p = 0) : d370850 p = 1 := by
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
  have h7 (q : Pattern) (selected : d46860 q = 0) : d320181 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d46860, d320181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46860, d320181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33351 q selected
  have h8 (q : Pattern) (selected : d46861 q = 0) : d320182 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d46861, d320182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46861, d320182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d46862 q = 0) : d320183 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d46862, d320183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46862, d320183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d46863 q = 0) : d320184 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d46863, d320184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46863, d320184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d370808 q = 0) : d370850 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d370808, d370850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d370808, d370850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h11 p selected
theorem eqIntro38901 (p : Pattern) (selected : d370814 p = 0) : d370856 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d370809 q = 0) : d370851 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d370809, d370851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38900 q selected
    | true =>
      simp only [d370809, d370851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d370810 q = 0) : d370852 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d370810, d370852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d370810, d370852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d370811 q = 0) : d370853 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d370811, d370853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d370811, d370853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d370812 q = 0) : d370854 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d370812, d370854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d370812, d370854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d370813 q = 0) : d370855 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d370813, d370855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d370813, d370855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d370814 q = 0) : d370856 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d370814, d370856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d370814, d370856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38902 (p : Pattern) (selected : d370819 p = 0) : d370861 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d370815 q = 0) : d370857 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d370815, d370857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38901 q selected
    | true =>
      simp only [d370815, d370857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d370816 q = 0) : d370858 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d370816, d370858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d370816, d370858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d370817 q = 0) : d370859 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d370817, d370859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d370817, d370859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d370818 q = 0) : d370860 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d370818, d370860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d370818, d370860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d370819 q = 0) : d370861 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d370819, d370861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d370819, d370861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro38903 (p : Pattern) (selected : d370825 p = 0) : d370867 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d370820 q = 0) : d370862 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d370820, d370862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38902 q selected
    | true =>
      simp only [d370820, d370862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d370821 q = 0) : d370863 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d370821, d370863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d370821, d370863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d370822 q = 0) : d370864 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d370822, d370864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d370822, d370864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d370823 q = 0) : d370865 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d370823, d370865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d370823, d370865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d370824 q = 0) : d370866 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d370824, d370866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d370824, d370866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d370825 q = 0) : d370867 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d370825, d370867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d370825, d370867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38904 (p : Pattern) (selected : d370831 p = 0) : d370873 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d370826 q = 0) : d370868 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d370826, d370868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38903 q selected
    | true =>
      simp only [d370826, d370868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d370827 q = 0) : d370869 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d370827, d370869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d370827, d370869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d370828 q = 0) : d370870 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d370828, d370870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d370828, d370870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d370829 q = 0) : d370871 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d370829, d370871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d370829, d370871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d370830 q = 0) : d370872 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d370830, d370872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d370830, d370872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d370831 q = 0) : d370873 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d370831, d370873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d370831, d370873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38905 (p : Pattern) (selected : d370837 p = 0) : d370879 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d370832 q = 0) : d370874 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d370832, d370874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38904 q selected
    | true =>
      simp only [d370832, d370874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d370833 q = 0) : d370875 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d370833, d370875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d370833, d370875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d370834 q = 0) : d370876 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d370834, d370876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d370834, d370876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d370835 q = 0) : d370877 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d370835, d370877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d370835, d370877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d370836 q = 0) : d370878 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d370836, d370878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d370836, d370878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d370837 q = 0) : d370879 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d370837, d370879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d370837, d370879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38906 (p : Pattern) (selected : d370843 p = 0) : d370885 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d370838 q = 0) : d370880 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d370838, d370880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38905 q selected
    | true =>
      simp only [d370838, d370880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d370839 q = 0) : d370881 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d370839, d370881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d370839, d370881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d370840 q = 0) : d370882 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d370840, d370882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d370840, d370882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d370841 q = 0) : d370883 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d370841, d370883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d370841, d370883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d370842 q = 0) : d370884 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d370842, d370884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d370842, d370884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d370843 q = 0) : d370885 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d370843, d370885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d370843, d370885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38907 (p : Pattern) (selected : d370849 p = 0) : d370891 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d370844 q = 0) : d370886 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d370844, d370886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38906 q selected
    | true =>
      simp only [d370844, d370886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d370845 q = 0) : d370887 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d370845, d370887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d370845, d370887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d370846 q = 0) : d370888 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d370846, d370888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d370846, d370888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d370847 q = 0) : d370889 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d370847, d370889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d370847, d370889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d370848 q = 0) : d370890 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d370848, d370890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d370848, d370890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d370849 q = 0) : d370891 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d370849, d370891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d370849, d370891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38908 (p : Pattern) (selected : d370808 p = 1) : d370892 p = 1 := by
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
  have h7 (q : Pattern) (selected : d46860 q = 1) : d321678 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d46860, d321678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46860, d321678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33559 q selected
  have h8 (q : Pattern) (selected : d46861 q = 1) : d321679 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d46861, d321679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46861, d321679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d46862 q = 1) : d321680 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d46862, d321680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46862, d321680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d46863 q = 1) : d322206 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d46863, d322206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46863, d322206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d370808 q = 1) : d370892 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d370808, d370892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d370808, d370892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h11 p selected
theorem eqIntro38909 (p : Pattern) (selected : d370814 p = 1) : d370898 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d370809 q = 1) : d370893 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d370809, d370893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38908 q selected
    | true =>
      simp only [d370809, d370893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d370810 q = 1) : d370894 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d370810, d370894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d370810, d370894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d370811 q = 1) : d370895 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d370811, d370895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d370811, d370895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d370812 q = 1) : d370896 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d370812, d370896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d370812, d370896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d370813 q = 1) : d370897 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d370813, d370897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d370813, d370897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d370814 q = 1) : d370898 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d370814, d370898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d370814, d370898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38910 (p : Pattern) (selected : d370819 p = 1) : d370903 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d370815 q = 1) : d370899 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d370815, d370899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38909 q selected
    | true =>
      simp only [d370815, d370899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d370816 q = 1) : d370900 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d370816, d370900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d370816, d370900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d370817 q = 1) : d370901 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d370817, d370901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d370817, d370901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d370818 q = 1) : d370902 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d370818, d370902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d370818, d370902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d370819 q = 1) : d370903 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d370819, d370903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d370819, d370903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro38911 (p : Pattern) (selected : d370825 p = 1) : d370909 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d370820 q = 1) : d370904 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d370820, d370904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38910 q selected
    | true =>
      simp only [d370820, d370904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d370821 q = 1) : d370905 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d370821, d370905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d370821, d370905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d370822 q = 1) : d370906 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d370822, d370906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d370822, d370906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d370823 q = 1) : d370907 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d370823, d370907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d370823, d370907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d370824 q = 1) : d370908 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d370824, d370908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d370824, d370908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d370825 q = 1) : d370909 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d370825, d370909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d370825, d370909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38912 (p : Pattern) (selected : d370831 p = 1) : d370915 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d370826 q = 1) : d370910 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d370826, d370910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38911 q selected
    | true =>
      simp only [d370826, d370910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d370827 q = 1) : d370911 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d370827, d370911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d370827, d370911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d370828 q = 1) : d370912 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d370828, d370912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d370828, d370912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d370829 q = 1) : d370913 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d370829, d370913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d370829, d370913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d370830 q = 1) : d370914 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d370830, d370914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d370830, d370914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d370831 q = 1) : d370915 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d370831, d370915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d370831, d370915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38913 (p : Pattern) (selected : d370837 p = 1) : d370921 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d370832 q = 1) : d370916 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d370832, d370916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38912 q selected
    | true =>
      simp only [d370832, d370916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d370833 q = 1) : d370917 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d370833, d370917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d370833, d370917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d370834 q = 1) : d370918 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d370834, d370918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d370834, d370918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d370835 q = 1) : d370919 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d370835, d370919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d370835, d370919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d370836 q = 1) : d370920 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d370836, d370920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d370836, d370920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d370837 q = 1) : d370921 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d370837, d370921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d370837, d370921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38914 (p : Pattern) (selected : d370843 p = 1) : d370927 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d370838 q = 1) : d370922 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d370838, d370922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38913 q selected
    | true =>
      simp only [d370838, d370922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d370839 q = 1) : d370923 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d370839, d370923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d370839, d370923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d370840 q = 1) : d370924 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d370840, d370924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d370840, d370924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d370841 q = 1) : d370925 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d370841, d370925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d370841, d370925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d370842 q = 1) : d370926 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d370842, d370926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d370842, d370926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d370843 q = 1) : d370927 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d370843, d370927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d370843, d370927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38915 (p : Pattern) (selected : d370849 p = 1) : d370933 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d370844 q = 1) : d370928 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d370844, d370928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38914 q selected
    | true =>
      simp only [d370844, d370928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d370845 q = 1) : d370929 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d370845, d370929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d370845, d370929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d370846 q = 1) : d370930 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d370846, d370930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d370846, d370930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d370847 q = 1) : d370931 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d370847, d370931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d370847, d370931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d370848 q = 1) : d370932 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d370848, d370932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d370848, d370932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d370849 q = 1) : d370933 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d370849, d370933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d370849, d370933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38916 (p : Pattern) (selected : d371356 p = 0) : d373066 p = 1 := by
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
  have h3 (q : Pattern) (selected : d339170 q = 0) : d341328 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d339170, d341328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d339170, d341328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d371354 q = 0) : d373064 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d371354, d373064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d371354, d373064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d339417 q = 0) : d341526 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d339417, d341526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d339417, d341526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
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
  have h7 (q : Pattern) (selected : d325306 q = 0) : d341090 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d325306, d341090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d325306, d341090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d371355 q = 0) : d373065 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d371355, d373065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d371355, d373065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d371356 q = 0) : d373066 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d371356, d373066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d371356, d373066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro38917 (p : Pattern) (selected : d371362 p = 0) : d373072 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d371357 q = 0) : d373067 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d371357, d373067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38916 q selected
    | true =>
      simp only [d371357, d373067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d371358 q = 0) : d373068 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d371358, d373068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d371358, d373068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d338998 q = 0) : d341205 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d338998, d341205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35287 q selected
    | true =>
      simp only [d338998, d341205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d338999 q = 0) : d341206 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d338999, d341206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d338999, d341206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d371359 q = 0) : d373069 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d371359, d373069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d371359, d373069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d338886 q = 0) : d341093 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d338886, d341093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35269 q selected
    | true =>
      simp only [d338886, d341093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d338887 q = 0) : d341094 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d338887, d341094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d338887, d341094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d339000 q = 0) : d341207 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d339000, d341207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d339000, d341207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d371360 q = 0) : d373070 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d371360, d373070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d371360, d373070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d371361 q = 0) : d373071 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d371361, d373071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d371361, d373071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d338888 q = 0) : d341095 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d338888, d341095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d338888, d341095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d339001 q = 0) : d341208 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d339001, d341208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d339001, d341208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d339002 q = 0) : d341209 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d339002, d341209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d339002, d341209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d371362 q = 0) : d373072 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d371362, d373072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d371362, d373072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  exact h14 p selected
theorem eqIntro38918 (p : Pattern) (selected : d371368 p = 0) : d373078 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d371363 q = 0) : d373073 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d371363, d373073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38917 q selected
    | true =>
      simp only [d371363, d373073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d371364 q = 0) : d373074 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d371364, d373074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d371364, d373074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d371365 q = 0) : d373075 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d371365, d373075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371365, d373075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d371366 q = 0) : d373076 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d371366, d373076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d371366, d373076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d339004 q = 0) : d341211 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d339004, d341211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35288 q selected
    | true =>
      simp only [d339004, d341211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d339005 q = 0) : d341212 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d339005, d341212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d339005, d341212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d339006 q = 0) : d341213 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d339006, d341213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d339006, d341213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d339007 q = 0) : d341214 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d339007, d341214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d339007, d341214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d371367 q = 0) : d373077 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d371367, d373077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d371367, d373077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d339191 q = 0) : d341349 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d339191, d341349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35321 q selected
    | true =>
      simp only [d339191, d341349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d339192 q = 0) : d341350 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d339192, d341350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d339192, d341350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d339193 q = 0) : d341351 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d339193, d341351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d339193, d341351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d339194 q = 0) : d341352 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d339194, d341352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d339194, d341352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d338892 q = 0) : d341099 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d338892, d341099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35270 q selected
    | true =>
      simp only [d338892, d341099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d338893 q = 0) : d341100 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d338893, d341100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d338893, d341100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d338894 q = 0) : d341101 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d338894, d341101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d338894, d341101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d338895 q = 0) : d341102 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d338895, d341102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d338895, d341102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d339195 q = 0) : d341353 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d339195, d341353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d339195, d341353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d371368 q = 0) : d373078 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d371368, d373078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d371368, d373078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro38919 (p : Pattern) (selected : d371374 p = 0) : d373084 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d371369 q = 0) : d373079 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d371369, d373079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38918 q selected
    | true =>
      simp only [d371369, d373079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35289 q selected
  have h2 (q : Pattern) (selected : d371370 q = 0) : d373080 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d371370, d373080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371370, d373080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d371371 q = 0) : d373081 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d371371, d373081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371371, d373081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d339010 q = 0) : d341217 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d339010, d341217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35289 q selected
    | true =>
      simp only [d339010, d341217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35271 q selected
  have h5 (q : Pattern) (selected : d339011 q = 0) : d341218 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d339011, d341218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d339011, d341218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d339012 q = 0) : d341219 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d339012, d341219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d339012, d341219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d371372 q = 0) : d373082 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d371372, d373082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d371372, d373082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d338898 q = 0) : d341105 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d338898, d341105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35271 q selected
    | true =>
      simp only [d338898, d341105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d338899 q = 0) : d341106 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d338899, d341106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d338899, d341106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d338900 q = 0) : d341107 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d338900, d341107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d338900, d341107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d339013 q = 0) : d341220 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d339013, d341220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d339013, d341220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d371373 q = 0) : d373083 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d371373, d373083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d371373, d373083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d371374 q = 0) : d373084 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d371374, d373084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d371374, d373084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro38920 (p : Pattern) (selected : d371380 p = 0) : d373090 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d371375 q = 0) : d373085 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d371375, d373085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38919 q selected
    | true =>
      simp only [d371375, d373085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d371376 q = 0) : d373086 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d371376, d373086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371376, d373086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d339016 q = 0) : d341223 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d339016, d341223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35290 q selected
    | true =>
      simp only [d339016, d341223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d339017 q = 0) : d341224 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d339017, d341224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d339017, d341224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d371377 q = 0) : d373087 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d371377, d373087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d371377, d373087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d371378 q = 0) : d373088 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d371378, d373088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d371378, d373088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d371379 q = 0) : d373089 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d371379, d373089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d371379, d373089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d371380 q = 0) : d373090 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d371380, d373090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371380, d373090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro38921 (p : Pattern) (selected : d371386 p = 0) : d373096 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d339160 q = 0) : d341318 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d339160, d341318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35316 q selected
    | true =>
      simp only [d339160, d341318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35285 q selected
  have h2 (q : Pattern) (selected : d339161 q = 0) : d341319 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d339161, d341319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d339161, d341319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d339162 q = 0) : d341320 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d339162, d341320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d339162, d341320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d339163 q = 0) : d341321 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d339163, d341321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d339163, d341321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d339167 q = 0) : d341325 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d339167, d341325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35317 q selected
    | true =>
      simp only [d339167, d341325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35286 q selected
  have h6 (q : Pattern) (selected : d339168 q = 0) : d341326 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d339168, d341326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d339168, d341326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d339169 q = 0) : d341327 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d339169, d341327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d339169, d341327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d371381 q = 0) : d373091 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d371381, d373091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38920 q selected
    | true =>
      simp only [d371381, d373091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35291 q selected
  have h9 (q : Pattern) (selected : d339237 q = 0) : d341229 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d339237, d341229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35329 q selected
    | true =>
      simp only [d339237, d341229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35296 q selected
  have h10 (q : Pattern) (selected : d371382 q = 0) : d373092 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d371382, d373092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d371382, d373092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d339243 q = 0) : d341373 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d339243, d341373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35330 q selected
    | true =>
      simp only [d339243, d341373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d339244 q = 0) : d341374 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d339244, d341374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d339244, d341374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d371383 q = 0) : d373093 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d371383, d373093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d371383, d373093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d371384 q = 0) : d373094 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d371384, d373094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d371384, d373094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d371385 q = 0) : d373095 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d371385, d373095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d371385, d373095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d371386 q = 0) : d373096 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d371386, d373096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371386, d373096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro38922 (p : Pattern) (selected : d371387 p = 0) : d373097 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d371375 q = 0) : d373085 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d371375, d373085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38919 q selected
    | true =>
      simp only [d371375, d373085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d371376 q = 0) : d373086 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d371376, d373086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371376, d373086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d339016 q = 0) : d341223 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d339016, d341223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35290 q selected
    | true =>
      simp only [d339016, d341223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d339017 q = 0) : d341224 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d339017, d341224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d339017, d341224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d371377 q = 0) : d373087 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d371377, d373087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d371377, d373087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d371378 q = 0) : d373088 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d371378, d373088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d371378, d373088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d371379 q = 0) : d373089 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d371379, d373089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d371379, d373089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d371387 q = 0) : d373097 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d371387, d373097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d371387, d373097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro38923 (p : Pattern) (selected : d371393 p = 0) : d373103 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d339160 q = 0) : d341318 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d339160, d341318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35316 q selected
    | true =>
      simp only [d339160, d341318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35285 q selected
  have h2 (q : Pattern) (selected : d339161 q = 0) : d341319 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d339161, d341319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d339161, d341319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d339162 q = 0) : d341320 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d339162, d341320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d339162, d341320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d339163 q = 0) : d341321 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d339163, d341321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d339163, d341321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d339167 q = 0) : d341325 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d339167, d341325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35317 q selected
    | true =>
      simp only [d339167, d341325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35286 q selected
  have h6 (q : Pattern) (selected : d339168 q = 0) : d341326 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d339168, d341326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d339168, d341326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d339169 q = 0) : d341327 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d339169, d341327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d339169, d341327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d371381 q = 0) : d373091 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d371381, d373091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38920 q selected
    | true =>
      simp only [d371381, d373091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35291 q selected
  have h9 (q : Pattern) (selected : d339237 q = 0) : d341229 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d339237, d341229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35329 q selected
    | true =>
      simp only [d339237, d341229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35296 q selected
  have h10 (q : Pattern) (selected : d371382 q = 0) : d373092 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d371382, d373092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d371382, d373092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d339243 q = 0) : d341373 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d339243, d341373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35330 q selected
    | true =>
      simp only [d339243, d341373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d339244 q = 0) : d341374 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d339244, d341374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d339244, d341374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d371383 q = 0) : d373093 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d371383, d373093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d371383, d373093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d371384 q = 0) : d373094 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d371384, d373094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d371384, d373094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d371385 q = 0) : d373095 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d371385, d373095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d371385, d373095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d339250 q = 0) : d341380 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d339250, d341380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35332 q selected
    | true =>
      simp only [d339250, d341380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35298 q selected
  have h17 (q : Pattern) (selected : d339251 q = 0) : d341381 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d339251, d341381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d339251, d341381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d339252 q = 0) : d341382 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d339252, d341382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d339252, d341382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d339253 q = 0) : d341383 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d339253, d341383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d339253, d341383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d339255 q = 0) : d341385 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d339255, d341385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35333 q selected
    | true =>
      simp only [d339255, d341385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35299 q selected
  have h21 (q : Pattern) (selected : d339256 q = 0) : d341386 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d339256, d341386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d339256, d341386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d339257 q = 0) : d341387 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d339257, d341387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d339257, d341387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d371388 q = 0) : d373098 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d371388, d373098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38922 q selected
    | true =>
      simp only [d371388, d373098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35300 q selected
  have h24 (q : Pattern) (selected : d339261 q = 0) : d341245 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d339261, d341245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35335 q selected
    | true =>
      simp only [d339261, d341245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35301 q selected
  have h25 (q : Pattern) (selected : d371389 q = 0) : d373099 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d371389, d373099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d371389, d373099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d339264 q = 0) : d341392 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d339264, d341392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35336 q selected
    | true =>
      simp only [d339264, d341392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d339265 q = 0) : d341393 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d339265, d341393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d339265, d341393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d371390 q = 0) : d373100 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d371390, d373100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d371390, d373100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d371391 q = 0) : d373101 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d371391, d373101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d371391, d373101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d371392 q = 0) : d373102 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d371392, d373102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d371392, d373102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d371393 q = 0) : d373103 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d371393, d373103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d371393, d373103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro38924 (p : Pattern) (selected : d371400 p = 0) : d373110 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d371388 q = 0) : d373098 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d371388, d373098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38922 q selected
    | true =>
      simp only [d371388, d373098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35300 q selected
  have h2 (q : Pattern) (selected : d339261 q = 0) : d341245 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d339261, d341245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35335 q selected
    | true =>
      simp only [d339261, d341245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35301 q selected
  have h3 (q : Pattern) (selected : d371389 q = 0) : d373099 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d371389, d373099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d371389, d373099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d339264 q = 0) : d341392 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d339264, d341392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35336 q selected
    | true =>
      simp only [d339264, d341392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d339265 q = 0) : d341393 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d339265, d341393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d339265, d341393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d371390 q = 0) : d373100 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d371390, d373100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d371390, d373100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d371398 q = 0) : d373108 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d371398, d373108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371398, d373108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d371399 q = 0) : d373109 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d371399, d373109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371399, d373109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d371400 q = 0) : d373110 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d371400, d373110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371400, d373110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro38925 (p : Pattern) (selected : d371411 p = 0) : d373121 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d371406 q = 0) : d373116 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d371406, d373116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371406, d373116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38917 q selected
  have h2 (q : Pattern) (selected : d371363 q = 0) : d373073 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d371363, d373073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38917 q selected
    | true =>
      simp only [d371363, d373073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d371407 q = 0) : d373117 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d371407, d373117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d371407, d373117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d371364 q = 0) : d373074 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d371364, d373074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d371364, d373074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d371408 q = 0) : d373118 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d371408, d373118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d371408, d373118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d371409 q = 0) : d373119 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d371409, d373119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d371409, d373119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d339088 q = 0) : d341265 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d339088, d341265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d339088, d341265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35288 q selected
  have h8 (q : Pattern) (selected : d339004 q = 0) : d341211 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d339004, d341211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35288 q selected
    | true =>
      simp only [d339004, d341211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d339089 q = 0) : d341266 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d339089, d341266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d339089, d341266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d339005 q = 0) : d341212 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d339005, d341212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d339005, d341212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d339090 q = 0) : d341267 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d339090, d341267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d339090, d341267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d339091 q = 0) : d341268 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d339091, d341268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d339091, d341268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d371410 q = 0) : d373120 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d371410, d373120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d371410, d373120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d339291 q = 0) : d341419 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d339291, d341419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d339291, d341419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35321 q selected
  have h15 (q : Pattern) (selected : d339191 q = 0) : d341349 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d339191, d341349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35321 q selected
    | true =>
      simp only [d339191, d341349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d339292 q = 0) : d341420 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d339292, d341420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d339292, d341420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d339192 q = 0) : d341350 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d339192, d341350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d339192, d341350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d339293 q = 0) : d341421 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d339293, d341421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d339293, d341421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d339294 q = 0) : d341422 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d339294, d341422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d339294, d341422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d338933 q = 0) : d341140 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d338933, d341140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d338933, d341140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35270 q selected
  have h21 (q : Pattern) (selected : d338892 q = 0) : d341099 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d338892, d341099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35270 q selected
    | true =>
      simp only [d338892, d341099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d338934 q = 0) : d341141 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d338934, d341141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d338934, d341141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d338893 q = 0) : d341100 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d338893, d341100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d338893, d341100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h24 (q : Pattern) (selected : d338935 q = 0) : d341142 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d338935, d341142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d338935, d341142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
  have h25 (q : Pattern) (selected : d338936 q = 0) : d341143 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d338936, d341143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
    | true =>
      simp only [d338936, d341143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h26 (q : Pattern) (selected : d339295 q = 0) : d341423 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d339295, d341423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d339295, d341423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d371411 q = 0) : d373121 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d371411, d373121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d371411, d373121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
theorem eqIntro38926 (p : Pattern) (selected : d371417 p = 0) : d373127 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d371412 q = 0) : d373122 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d371412, d373122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38925 q selected
    | true =>
      simp only [d371412, d373122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35305 q selected
  have h2 (q : Pattern) (selected : d371413 q = 0) : d373123 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d371413, d373123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371413, d373123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d371414 q = 0) : d373124 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d371414, d373124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371414, d373124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d339094 q = 0) : d341271 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d339094, d341271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35305 q selected
    | true =>
      simp only [d339094, d341271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35278 q selected
  have h5 (q : Pattern) (selected : d339095 q = 0) : d341272 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d339095, d341272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d339095, d341272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d339096 q = 0) : d341273 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d339096, d341273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d339096, d341273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d371415 q = 0) : d373125 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d371415, d373125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d371415, d373125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d338939 q = 0) : d341146 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d338939, d341146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35278 q selected
    | true =>
      simp only [d338939, d341146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d338940 q = 0) : d341147 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d338940, d341147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d338940, d341147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d338941 q = 0) : d341148 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d338941, d341148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d338941, d341148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d339097 q = 0) : d341274 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d339097, d341274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d339097, d341274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d371416 q = 0) : d373126 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d371416, d373126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d371416, d373126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d371417 q = 0) : d373127 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d371417, d373127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d371417, d373127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro38927 (p : Pattern) (selected : d371423 p = 0) : d373133 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d371418 q = 0) : d373128 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d371418, d373128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38926 q selected
    | true =>
      simp only [d371418, d373128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d371419 q = 0) : d373129 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d371419, d373129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371419, d373129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d339100 q = 0) : d341277 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d339100, d341277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35306 q selected
    | true =>
      simp only [d339100, d341277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d339101 q = 0) : d341278 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d339101, d341278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d339101, d341278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d371420 q = 0) : d373130 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d371420, d373130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d371420, d373130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d371421 q = 0) : d373131 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d371421, d373131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d371421, d373131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d371422 q = 0) : d373132 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d371422, d373132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d371422, d373132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d371423 q = 0) : d373133 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d371423, d373133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d371423, d373133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro38928 (p : Pattern) (selected : d371429 p = 0) : d373139 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d371424 q = 0) : d373134 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d371424, d373134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38927 q selected
    | true =>
      simp only [d371424, d373134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35307 q selected
  have h2 (q : Pattern) (selected : d339328 q = 0) : d341283 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d339328, d341283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35346 q selected
    | true =>
      simp only [d339328, d341283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35310 q selected
  have h3 (q : Pattern) (selected : d371425 q = 0) : d373135 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d371425, d373135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d371425, d373135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d339334 q = 0) : d341443 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d339334, d341443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35347 q selected
    | true =>
      simp only [d339334, d341443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d339335 q = 0) : d341444 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d339335, d341444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d339335, d341444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d371426 q = 0) : d373136 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d371426, d373136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d371426, d373136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d371427 q = 0) : d373137 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d371427, d373137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371427, d373137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d371428 q = 0) : d373138 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d371428, d373138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371428, d373138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d371429 q = 0) : d373139 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d371429, d373139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371429, d373139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro38929 (p : Pattern) (selected : d371435 p = 0) : d373145 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d339148 q = 0) : d341306 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d339148, d341306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d339148, d341306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35314 q selected
  have h2 (q : Pattern) (selected : d339149 q = 0) : d341307 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d339149, d341307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d339149, d341307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d339155 q = 0) : d341313 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d339155, d341313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35314 q selected
    | true =>
      simp only [d339155, d341313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35315 q selected
  have h4 (q : Pattern) (selected : d339156 q = 0) : d341314 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d339156, d341314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d339156, d341314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d339157 q = 0) : d341315 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d339157, d341315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d339157, d341315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d371394 q = 0) : d373104 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d371394, d373104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38921 q selected
    | true =>
      simp only [d371394, d373104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38923 q selected
  have h7 (q : Pattern) (selected : d339272 q = 0) : d341400 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d339272, d341400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35338 q selected
    | true =>
      simp only [d339272, d341400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35284 q selected
  have h8 (q : Pattern) (selected : d371395 q = 0) : d373105 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d371395, d373105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d371395, d373105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d371396 q = 0) : d373106 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d371396, d373106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d371396, d373106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d371397 q = 0) : d373107 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d371397, d373107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d371397, d373107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d371401 q = 0) : d373111 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d371401, d373111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371401, d373111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38924 q selected
  have h12 (q : Pattern) (selected : d339281 q = 0) : d341409 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d339281, d341409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d339281, d341409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35340 q selected
  have h13 (q : Pattern) (selected : d371402 q = 0) : d373112 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d371402, d373112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d371402, d373112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d371403 q = 0) : d373113 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d371403, d373113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d371403, d373113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d371404 q = 0) : d373114 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d371404, d373114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d371404, d373114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d371405 q = 0) : d373115 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d371405, d373115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d371405, d373115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d371430 q = 0) : d373140 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d371430, d373140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371430, d373140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38928 q selected
  have h18 (q : Pattern) (selected : d339346 q = 0) : d341455 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d339346, d341455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d339346, d341455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35349 q selected
  have h19 (q : Pattern) (selected : d371431 q = 0) : d373141 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d371431, d373141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d371431, d373141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d371432 q = 0) : d373142 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d371432, d373142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d371432, d373142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d371433 q = 0) : d373143 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d371433, d373143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d371433, d373143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d371434 q = 0) : d373144 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d371434, d373144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d371434, d373144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d371435 q = 0) : d373145 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d371435, d373145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d371435, d373145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro38930 (p : Pattern) (selected : d371441 p = 0) : d373151 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d371436 q = 0) : d373146 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d371436, d373146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371436, d373146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38929 q selected
  have h2 (q : Pattern) (selected : d371437 q = 0) : d373147 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d371437, d373147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371437, d373147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d371438 q = 0) : d373148 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d371438, d373148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371438, d373148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d371439 q = 0) : d373149 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d371439, d373149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371439, d373149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d371440 q = 0) : d373150 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d371440, d373150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371440, d373150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d371441 q = 0) : d373151 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d371441, d373151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371441, d373151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro38931 (p : Pattern) (selected : d371444 p = 0) : d373154 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d371369 q = 0) : d373079 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d371369, d373079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38918 q selected
    | true =>
      simp only [d371369, d373079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35289 q selected
  have h2 (q : Pattern) (selected : d371370 q = 0) : d373080 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d371370, d373080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371370, d373080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d371371 q = 0) : d373081 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d371371, d373081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371371, d373081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d339010 q = 0) : d341217 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d339010, d341217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35289 q selected
    | true =>
      simp only [d339010, d341217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35271 q selected
  have h5 (q : Pattern) (selected : d339011 q = 0) : d341218 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d339011, d341218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d339011, d341218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d339012 q = 0) : d341219 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d339012, d341219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d339012, d341219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d371372 q = 0) : d373082 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d371372, d373082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d371372, d373082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d339359 q = 0) : d341468 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d339359, d341468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d339359, d341468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d371443 q = 0) : d373153 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d371443, d373153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d371443, d373153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d371444 q = 0) : d373154 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d371444, d373154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d371444, d373154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro38932 (p : Pattern) (selected : d371450 p = 0) : d373160 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d371445 q = 0) : d373155 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d371445, d373155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38931 q selected
    | true =>
      simp only [d371445, d373155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d371446 q = 0) : d373156 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d371446, d373156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371446, d373156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d339366 q = 0) : d341475 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d339366, d341475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35353 q selected
    | true =>
      simp only [d339366, d341475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d339367 q = 0) : d341476 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d339367, d341476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d339367, d341476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d371447 q = 0) : d373157 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d371447, d373157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d371447, d373157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d371448 q = 0) : d373158 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d371448, d373158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d371448, d373158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d371449 q = 0) : d373159 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d371449, d373159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d371449, d373159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d371450 q = 0) : d373160 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d371450, d373160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371450, d373160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro38933 (p : Pattern) (selected : d371456 p = 0) : d373166 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d371451 q = 0) : d373161 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d371451, d373161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38932 q selected
    | true =>
      simp only [d371451, d373161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35355 q selected
  have h2 (q : Pattern) (selected : d371452 q = 0) : d373162 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d371452, d373162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371452, d373162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d371453 q = 0) : d373163 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d371453, d373163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d371453, d373163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d371454 q = 0) : d373164 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d371454, d373164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371454, d373164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d371455 q = 0) : d373165 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d371455, d373165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371455, d373165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d371456 q = 0) : d373166 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d371456, d373166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371456, d373166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro38934 (p : Pattern) (selected : d371459 p = 0) : d373169 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d371445 q = 0) : d373155 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d371445, d373155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38931 q selected
    | true =>
      simp only [d371445, d373155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d371446 q = 0) : d373156 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d371446, d373156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371446, d373156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d339366 q = 0) : d341475 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d339366, d341475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35353 q selected
    | true =>
      simp only [d339366, d341475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d339367 q = 0) : d341476 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d339367, d341476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d339367, d341476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d371447 q = 0) : d373157 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d371447, d373157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d371447, d373157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d371448 q = 0) : d373158 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d371448, d373158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d371448, d373158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d371449 q = 0) : d373159 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d371449, d373159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d371449, d373159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d371459 q = 0) : d373169 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d371459, d373169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d371459, d373169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro38935 (p : Pattern) (selected : d371465 p = 0) : d373175 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d371451 q = 0) : d373161 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d371451, d373161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38932 q selected
    | true =>
      simp only [d371451, d373161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35355 q selected
  have h2 (q : Pattern) (selected : d371452 q = 0) : d373162 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d371452, d373162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371452, d373162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d371453 q = 0) : d373163 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d371453, d373163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d371453, d373163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d371454 q = 0) : d373164 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d371454, d373164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371454, d373164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d371455 q = 0) : d373165 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d371455, d373165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371455, d373165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d371460 q = 0) : d373170 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d371460, d373170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38934 q selected
    | true =>
      simp only [d371460, d373170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35358 q selected
  have h7 (q : Pattern) (selected : d371461 q = 0) : d373171 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d371461, d373171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371461, d373171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d371462 q = 0) : d373172 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d371462, d373172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d371462, d373172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d371463 q = 0) : d373173 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d371463, d373173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371463, d373173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d371464 q = 0) : d373174 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d371464, d373174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371464, d373174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d371465 q = 0) : d373175 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d371465, d373175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d371465, d373175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro38936 (p : Pattern) (selected : d371470 p = 0) : d373180 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d371445 q = 0) : d373155 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d371445, d373155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38931 q selected
    | true =>
      simp only [d371445, d373155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d371446 q = 0) : d373156 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d371446, d373156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371446, d373156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d339366 q = 0) : d341475 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d339366, d341475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35353 q selected
    | true =>
      simp only [d339366, d341475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d339367 q = 0) : d341476 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d339367, d341476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d339367, d341476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d371447 q = 0) : d373157 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d371447, d373157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d371447, d373157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d371448 q = 0) : d373158 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d371448, d373158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d371448, d373158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d371469 q = 0) : d373179 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d371469, d373179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371469, d373179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d371470 q = 0) : d373180 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d371470, d373180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371470, d373180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro38937 (p : Pattern) (selected : d371477 p = 0) : d373187 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d371445 q = 0) : d373155 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d371445, d373155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38931 q selected
    | true =>
      simp only [d371445, d373155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d371446 q = 0) : d373156 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d371446, d373156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371446, d373156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d339366 q = 0) : d341475 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d339366, d341475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35353 q selected
    | true =>
      simp only [d339366, d341475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d339367 q = 0) : d341476 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d339367, d341476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d339367, d341476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d371447 q = 0) : d373157 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d371447, d373157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d371447, d373157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d371475 q = 0) : d373185 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d371475, d373185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371475, d373185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d371476 q = 0) : d373186 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d371476, d373186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d371476, d373186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d371477 q = 0) : d373187 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d371477, d373187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371477, d373187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro38938 (p : Pattern) (selected : d371482 p = 0) : d373192 p = 1 := by
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
  have h3 (q : Pattern) (selected : d339417 q = 0) : d341526 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d339417, d341526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d339417, d341526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13 q = 0) : d127 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d325306 q = 0) : d341090 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d325306, d341090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d325306, d341090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d371355 q = 0) : d373065 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d371355, d373065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d371355, d373065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d338884 q = 0) : d341091 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d338884, d341091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d338884, d341091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d371482 q = 0) : d373192 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d371482, d373192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d371482, d373192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro38939 (p : Pattern) (selected : d371491 p = 0) : d373201 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d371357 q = 0) : d373067 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d371357, d373067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38916 q selected
    | true =>
      simp only [d371357, d373067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d371358 q = 0) : d373068 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d371358, d373068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d371358, d373068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d371481 q = 0) : d373191 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d371481, d373191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371481, d373191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d371483 q = 0) : d373193 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d371483, d373193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38938 q selected
    | true =>
      simp only [d371483, d373193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d371484 q = 0) : d373194 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d371484, d373194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d371484, d373194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d371485 q = 0) : d373195 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d371485, d373195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d371485, d373195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d371486 q = 0) : d373196 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d371486, d373196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d371486, d373196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d371487 q = 0) : d373197 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d371487, d373197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d371487, d373197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d338998 q = 0) : d341205 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d338998, d341205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35287 q selected
    | true =>
      simp only [d338998, d341205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d338999 q = 0) : d341206 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d338999, d341206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d338999, d341206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d371359 q = 0) : d373069 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d371359, d373069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d371359, d373069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d338886 q = 0) : d341093 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d338886, d341093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35269 q selected
    | true =>
      simp only [d338886, d341093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d338887 q = 0) : d341094 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d338887, d341094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d338887, d341094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d371488 q = 0) : d373198 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d371488, d373198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d371488, d373198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d371489 q = 0) : d373199 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d371489, d373199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d371489, d373199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d371490 q = 0) : d373200 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d371490, d373200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d371490, d373200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d371491 q = 0) : d373201 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d371491, d373201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d371491, d373201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro38940 (p : Pattern) (selected : d371500 p = 0) : d373210 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d371357 q = 0) : d373067 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d371357, d373067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38916 q selected
    | true =>
      simp only [d371357, d373067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d371358 q = 0) : d373068 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d371358, d373068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d371358, d373068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d338998 q = 0) : d341205 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d338998, d341205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35287 q selected
    | true =>
      simp only [d338998, d341205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d338999 q = 0) : d341206 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d338999, d341206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d338999, d341206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d371359 q = 0) : d373069 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d371359, d373069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d371359, d373069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d338886 q = 0) : d341093 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d338886, d341093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35269 q selected
    | true =>
      simp only [d338886, d341093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d338887 q = 0) : d341094 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d338887, d341094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d338887, d341094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d339000 q = 0) : d341207 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d339000, d341207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d339000, d341207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d371360 q = 0) : d373070 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d371360, d373070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d371360, d373070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d371361 q = 0) : d373071 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d371361, d373071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d371361, d373071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d340557 q = 0) : d342321 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d340557, d342321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35573 q selected
    | true =>
      simp only [d340557, d342321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d371496 q = 0) : d373206 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d371496, d373206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d371496, d373206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d371497 q = 0) : d373207 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d371497, d373207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d371497, d373207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h14 (q : Pattern) (selected : d371498 q = 0) : d373208 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d371498, d373208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d371498, d373208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d371499 q = 0) : d373209 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d371499, d373209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d371499, d373209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d371500 q = 0) : d373210 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d371500, d373210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d371500, d373210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro38941 (p : Pattern) (selected : d371509 p = 0) : d373219 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d371357 q = 0) : d373067 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d371357, d373067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38916 q selected
    | true =>
      simp only [d371357, d373067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d371358 q = 0) : d373068 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d371358, d373068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d371358, d373068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d340557 q = 0) : d342321 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d340557, d342321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35573 q selected
    | true =>
      simp only [d340557, d342321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d371496 q = 0) : d373206 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d371496, d373206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d371496, d373206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d371506 q = 0) : d373216 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d371506, d373216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d371506, d373216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d371507 q = 0) : d373217 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d371507, d373217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d371507, d373217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d371508 q = 0) : d373218 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d371508, d373218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d371508, d373218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d338886 q = 0) : d341093 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d338886, d341093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35269 q selected
    | true =>
      simp only [d338886, d341093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d338887 q = 0) : d341094 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d338887, d341094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d338887, d341094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d371497 q = 0) : d373207 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d371497, d373207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d371497, d373207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d371498 q = 0) : d373208 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d371498, d373208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d371498, d373208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d371499 q = 0) : d373209 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d371499, d373209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d371499, d373209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d371509 q = 0) : d373219 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d371509, d373219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d371509, d373219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro38942 (p : Pattern) (selected : d371515 p = 0) : d373225 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d371492 q = 0) : d373202 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d371492, d373202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38939 q selected
    | true =>
      simp only [d371492, d373202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d371493 q = 0) : d373203 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d371493, d373203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d371493, d373203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d371494 q = 0) : d373204 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d371494, d373204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371494, d373204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d371495 q = 0) : d373205 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d371495, d373205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d371495, d373205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d371501 q = 0) : d373211 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d371501, d373211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38940 q selected
    | true =>
      simp only [d371501, d373211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d371502 q = 0) : d373212 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d371502, d373212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d371502, d373212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d371503 q = 0) : d373213 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d371503, d373213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371503, d373213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d371504 q = 0) : d373214 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d371504, d373214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d371504, d373214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d371505 q = 0) : d373215 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d371505, d373215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d371505, d373215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d371510 q = 0) : d373220 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d371510, d373220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38941 q selected
    | true =>
      simp only [d371510, d373220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d371511 q = 0) : d373221 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d371511, d373221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d371511, d373221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d371512 q = 0) : d373222 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d371512, d373222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371512, d373222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d371513 q = 0) : d373223 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d371513, d373223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d371513, d373223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d339191 q = 0) : d341349 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d339191, d341349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35321 q selected
    | true =>
      simp only [d339191, d341349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d339192 q = 0) : d341350 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d339192, d341350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d339192, d341350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d339193 q = 0) : d341351 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d339193, d341351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d339193, d341351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d339194 q = 0) : d341352 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d339194, d341352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d339194, d341352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d371514 q = 0) : d373224 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d371514, d373224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d371514, d373224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d371515 q = 0) : d373225 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d371515, d373225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d371515, d373225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro38943 (p : Pattern) (selected : d371524 p = 0) : d373234 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d371516 q = 0) : d373226 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d371516, d373226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38942 q selected
    | true =>
      simp only [d371516, d373226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38918 q selected
  have h2 (q : Pattern) (selected : d371517 q = 0) : d373227 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d371517, d373227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371517, d373227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d371518 q = 0) : d373228 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d371518, d373228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371518, d373228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d371519 q = 0) : d373229 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d371519, d373229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38918 q selected
    | true =>
      simp only [d371519, d373229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35371 q selected
  have h5 (q : Pattern) (selected : d371520 q = 0) : d373230 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d371520, d373230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371520, d373230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d371521 q = 0) : d373231 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d371521, d373231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371521, d373231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d371522 q = 0) : d373232 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d371522, d373232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d371522, d373232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d371369 q = 0) : d373079 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d371369, d373079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38918 q selected
    | true =>
      simp only [d371369, d373079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35289 q selected
  have h9 (q : Pattern) (selected : d371370 q = 0) : d373080 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d371370, d373080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371370, d373080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d371371 q = 0) : d373081 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d371371, d373081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371371, d373081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d339010 q = 0) : d341217 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d339010, d341217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35289 q selected
    | true =>
      simp only [d339010, d341217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35271 q selected
  have h12 (q : Pattern) (selected : d339011 q = 0) : d341218 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d339011, d341218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d339011, d341218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d339012 q = 0) : d341219 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d339012, d341219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d339012, d341219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d371372 q = 0) : d373082 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d371372, d373082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d371372, d373082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d371523 q = 0) : d373233 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d371523, d373233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d371523, d373233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d371524 q = 0) : d373234 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d371524, d373234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d371524, d373234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro38944 (p : Pattern) (selected : d371530 p = 0) : d373240 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d371525 q = 0) : d373235 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d371525, d373235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38943 q selected
    | true =>
      simp only [d371525, d373235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d371526 q = 0) : d373236 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d371526, d373236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371526, d373236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d371445 q = 0) : d373155 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d371445, d373155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38931 q selected
    | true =>
      simp only [d371445, d373155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d371446 q = 0) : d373156 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d371446, d373156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371446, d373156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d371527 q = 0) : d373237 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d371527, d373237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d371527, d373237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d371528 q = 0) : d373238 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d371528, d373238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d371528, d373238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d371529 q = 0) : d373239 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d371529, d373239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d371529, d373239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d371530 q = 0) : d373240 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d371530, d373240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371530, d373240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro38945 (p : Pattern) (selected : d371534 p = 0) : d373066 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2 q = 0) : d0 q = 1 := by
    change (2 : Int) = 0 at selected
    omega
  have h2 (q : Pattern) (selected : d338 q = 0) : d13 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d338, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d338, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d339469 q = 0) : d341328 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d339469, d341328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d339469, d341328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d371532 q = 0) : d373064 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d371532, d373064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d371532, d373064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d339816 q = 0) : d341526 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d339816, d341526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d339816, d341526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d158 q = 0) : d127 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d158, d127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d158, d127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d339023 q = 0) : d341090 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d339023, d341090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d339023, d341090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d371533 q = 0) : d373065 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d371533, d373065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d371533, d373065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d371534 q = 0) : d373066 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d371534, d373066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d371534, d373066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro38946 (p : Pattern) (selected : d371540 p = 0) : d373072 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d371535 q = 0) : d373067 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d371535, d373067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38945 q selected
    | true =>
      simp only [d371535, d373067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d371536 q = 0) : d373068 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d371536, d373068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d371536, d373068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d339213 q = 0) : d341205 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d339213, d341205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35325 q selected
    | true =>
      simp only [d339213, d341205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d339214 q = 0) : d341206 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d339214, d341206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d339214, d341206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d371537 q = 0) : d373069 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d371537, d373069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d371537, d373069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d339026 q = 0) : d341093 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d339026, d341093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35292 q selected
    | true =>
      simp only [d339026, d341093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d339027 q = 0) : d341094 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d339027, d341094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d339027, d341094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d339215 q = 0) : d341207 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d339215, d341207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d339215, d341207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d371538 q = 0) : d373070 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d371538, d373070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d371538, d373070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d371539 q = 0) : d373071 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d371539, d373071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d371539, d373071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d339028 q = 0) : d341095 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d339028, d341095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d339028, d341095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d339216 q = 0) : d341208 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d339216, d341208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d339216, d341208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d339217 q = 0) : d341209 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d339217, d341209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d339217, d341209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d371540 q = 0) : d373072 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d371540, d373072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d371540, d373072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  exact h14 p selected
theorem eqIntro38947 (p : Pattern) (selected : d371546 p = 0) : d373078 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d371541 q = 0) : d373073 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d371541, d373073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38946 q selected
    | true =>
      simp only [d371541, d373073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d371542 q = 0) : d373074 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d371542, d373074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d371542, d373074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d371543 q = 0) : d373075 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d371543, d373075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371543, d373075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d371544 q = 0) : d373076 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d371544, d373076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d371544, d373076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d339219 q = 0) : d341211 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d339219, d341211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35326 q selected
    | true =>
      simp only [d339219, d341211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d339220 q = 0) : d341212 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d339220, d341212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d339220, d341212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d339221 q = 0) : d341213 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d339221, d341213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d339221, d341213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d339222 q = 0) : d341214 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d339222, d341214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d339222, d341214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d371545 q = 0) : d373077 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d371545, d373077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d371545, d373077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d339490 q = 0) : d341349 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d339490, d341349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35377 q selected
    | true =>
      simp only [d339490, d341349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d339491 q = 0) : d341350 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d339491, d341350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d339491, d341350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d339492 q = 0) : d341351 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d339492, d341351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d339492, d341351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d339493 q = 0) : d341352 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d339493, d341352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d339493, d341352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d339032 q = 0) : d341099 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d339032, d341099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35293 q selected
    | true =>
      simp only [d339032, d341099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d339033 q = 0) : d341100 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d339033, d341100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d339033, d341100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d339034 q = 0) : d341101 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d339034, d341101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d339034, d341101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d339035 q = 0) : d341102 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d339035, d341102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d339035, d341102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d339494 q = 0) : d341353 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d339494, d341353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d339494, d341353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d371546 q = 0) : d373078 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d371546, d373078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d371546, d373078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro38948 (p : Pattern) (selected : d371552 p = 0) : d373154 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d371547 q = 0) : d373079 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d371547, d373079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38947 q selected
    | true =>
      simp only [d371547, d373079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35327 q selected
  have h2 (q : Pattern) (selected : d371548 q = 0) : d373080 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d371548, d373080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371548, d373080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d371549 q = 0) : d373081 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d371549, d373081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371549, d373081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d339225 q = 0) : d341217 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d339225, d341217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35327 q selected
    | true =>
      simp only [d339225, d341217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35294 q selected
  have h5 (q : Pattern) (selected : d339226 q = 0) : d341218 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d339226, d341218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d339226, d341218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d339227 q = 0) : d341219 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d339227, d341219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d339227, d341219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d371550 q = 0) : d373082 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d371550, d373082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d371550, d373082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d339500 q = 0) : d341468 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d339500, d341468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d339500, d341468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d371551 q = 0) : d373153 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d371551, d373153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d371551, d373153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d371552 q = 0) : d373154 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d371552, d373154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d371552, d373154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro38949 (p : Pattern) (selected : d371558 p = 0) : d373160 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d371553 q = 0) : d373155 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d371553, d373155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38948 q selected
    | true =>
      simp only [d371553, d373155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d371554 q = 0) : d373156 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d371554, d373156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371554, d373156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d339507 q = 0) : d341475 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d339507, d341475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35380 q selected
    | true =>
      simp only [d339507, d341475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d339508 q = 0) : d341476 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d339508, d341476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d339508, d341476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d371555 q = 0) : d373157 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d371555, d373157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d371555, d373157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d371556 q = 0) : d373158 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d371556, d373158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d371556, d373158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d371557 q = 0) : d373159 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d371557, d373159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d371557, d373159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d371558 q = 0) : d373160 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d371558, d373160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371558, d373160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro38950 (p : Pattern) (selected : d371564 p = 0) : d373246 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d371445 q = 0) : d373155 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d371445, d373155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38931 q selected
    | true =>
      simp only [d371445, d373155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d371446 q = 0) : d373156 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d371446, d373156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371446, d373156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d371561 q = 0) : d373243 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d371561, d373243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d371561, d373243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d371562 q = 0) : d373244 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d371562, d373244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d371562, d373244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d371563 q = 0) : d373245 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d371563, d373245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d371563, d373245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d371564 q = 0) : d373246 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d371564, d373246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371564, d373246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro38951 (p : Pattern) (selected : d371570 p = 0) : d373252 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d371471 q = 0) : d373181 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d371471, d373181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38936 q selected
    | true =>
      simp only [d371471, d373181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35361 q selected
  have h2 (q : Pattern) (selected : d371472 q = 0) : d373182 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d371472, d373182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371472, d373182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d371473 q = 0) : d373183 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d371473, d373183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d371473, d373183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d371474 q = 0) : d373184 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d371474, d373184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371474, d373184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d371478 q = 0) : d373188 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d371478, d373188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38937 q selected
    | true =>
      simp only [d371478, d373188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35363 q selected
  have h6 (q : Pattern) (selected : d371479 q = 0) : d373189 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d371479, d373189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371479, d373189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d371480 q = 0) : d373190 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d371480, d373190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d371480, d373190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d371531 q = 0) : d373241 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d371531, d373241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38944 q selected
    | true =>
      simp only [d371531, d373241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38932 q selected
  have h9 (q : Pattern) (selected : d371559 q = 0) : d373161 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d371559, d373161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38949 q selected
    | true =>
      simp only [d371559, d373161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35382 q selected
  have h10 (q : Pattern) (selected : d371560 q = 0) : d373242 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d371560, d373242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d371560, d373242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d371565 q = 0) : d373247 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d371565, d373247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38950 q selected
    | true =>
      simp only [d371565, d373247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d371566 q = 0) : d373248 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d371566, d373248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d371566, d373248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d371567 q = 0) : d373249 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d371567, d373249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d371567, d373249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d371568 q = 0) : d373250 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d371568, d373250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d371568, d373250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d371569 q = 0) : d373251 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d371569, d373251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d371569, d373251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d371570 q = 0) : d373252 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d371570, d373252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371570, d373252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro38952 (p : Pattern) (selected : d371571 p = 0) : d373253 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d371445 q = 0) : d373155 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d371445, d373155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38931 q selected
    | true =>
      simp only [d371445, d373155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d371446 q = 0) : d373156 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d371446, d373156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371446, d373156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d339366 q = 0) : d341475 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d339366, d341475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35353 q selected
    | true =>
      simp only [d339366, d341475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d339367 q = 0) : d341476 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d339367, d341476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d339367, d341476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d371447 q = 0) : d373157 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d371447, d373157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d371447, d373157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d371448 q = 0) : d373158 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d371448, d373158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d371448, d373158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d371469 q = 0) : d373179 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d371469, d373179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371469, d373179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d371571 q = 0) : d373253 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d371571, d373253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d371571, d373253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro38953 (p : Pattern) (selected : d371576 p = 0) : d373258 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d371445 q = 0) : d373155 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d371445, d373155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38931 q selected
    | true =>
      simp only [d371445, d373155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d371446 q = 0) : d373156 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d371446, d373156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371446, d373156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d339366 q = 0) : d341475 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d339366, d341475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35353 q selected
    | true =>
      simp only [d339366, d341475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d339367 q = 0) : d341476 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d339367, d341476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d339367, d341476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d371447 q = 0) : d373157 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d371447, d373157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d371447, d373157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d371475 q = 0) : d373185 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d371475, d373185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371475, d373185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d371476 q = 0) : d373186 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d371476, d373186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d371476, d373186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d371576 q = 0) : d373258 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d371576, d373258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d371576, d373258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro38954 (p : Pattern) (selected : d371580 p = 0) : d373262 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d371525 q = 0) : d373235 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d371525, d373235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38943 q selected
    | true =>
      simp only [d371525, d373235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d371526 q = 0) : d373236 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d371526, d373236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371526, d373236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d371445 q = 0) : d373155 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d371445, d373155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38931 q selected
    | true =>
      simp only [d371445, d373155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d371446 q = 0) : d373156 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d371446, d373156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371446, d373156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d371527 q = 0) : d373237 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d371527, d373237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d371527, d373237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d371528 q = 0) : d373238 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d371528, d373238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d371528, d373238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d371529 q = 0) : d373239 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d371529, d373239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d371529, d373239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d371580 q = 0) : d373262 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d371580, d373262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d371580, d373262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro38955 (p : Pattern) (selected : d371582 p = 0) : d373169 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d371553 q = 0) : d373155 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d371553, d373155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38948 q selected
    | true =>
      simp only [d371553, d373155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d371554 q = 0) : d373156 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d371554, d373156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371554, d373156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d339507 q = 0) : d341475 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d339507, d341475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35380 q selected
    | true =>
      simp only [d339507, d341475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d339508 q = 0) : d341476 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d339508, d341476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d339508, d341476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d371555 q = 0) : d373157 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d371555, d373157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d371555, d373157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d371556 q = 0) : d373158 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d371556, d373158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d371556, d373158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d371557 q = 0) : d373159 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d371557, d373159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d371557, d373159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d371582 q = 0) : d373169 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d371582, d373169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d371582, d373169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro38956 (p : Pattern) (selected : d371585 p = 0) : d373265 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d371445 q = 0) : d373155 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d371445, d373155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38931 q selected
    | true =>
      simp only [d371445, d373155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d371446 q = 0) : d373156 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d371446, d373156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371446, d373156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d371561 q = 0) : d373243 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d371561, d373243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d371561, d373243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d371562 q = 0) : d373244 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d371562, d373244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d371562, d373244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d371563 q = 0) : d373245 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d371563, d373245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d371563, d373245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d371585 q = 0) : d373265 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d371585, d373265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d371585, d373265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38957 (p : Pattern) (selected : d371591 p = 0) : d373271 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d371471 q = 0) : d373181 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d371471, d373181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38936 q selected
    | true =>
      simp only [d371471, d373181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35361 q selected
  have h2 (q : Pattern) (selected : d371472 q = 0) : d373182 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d371472, d373182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371472, d373182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d371473 q = 0) : d373183 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d371473, d373183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d371473, d373183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d371474 q = 0) : d373184 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d371474, d373184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371474, d373184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d371478 q = 0) : d373188 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d371478, d373188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38937 q selected
    | true =>
      simp only [d371478, d373188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35363 q selected
  have h6 (q : Pattern) (selected : d371479 q = 0) : d373189 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d371479, d373189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371479, d373189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d371480 q = 0) : d373190 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d371480, d373190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d371480, d373190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d371531 q = 0) : d373241 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d371531, d373241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38944 q selected
    | true =>
      simp only [d371531, d373241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38932 q selected
  have h9 (q : Pattern) (selected : d371559 q = 0) : d373161 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d371559, d373161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38949 q selected
    | true =>
      simp only [d371559, d373161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35382 q selected
  have h10 (q : Pattern) (selected : d371560 q = 0) : d373242 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d371560, d373242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d371560, d373242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d371565 q = 0) : d373247 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d371565, d373247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38950 q selected
    | true =>
      simp only [d371565, d373247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d371566 q = 0) : d373248 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d371566, d373248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d371566, d373248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d371567 q = 0) : d373249 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d371567, d373249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d371567, d373249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d371568 q = 0) : d373250 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d371568, d373250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d371568, d373250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d371569 q = 0) : d373251 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d371569, d373251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d371569, d373251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d371572 q = 0) : d373254 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d371572, d373254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38952 q selected
    | true =>
      simp only [d371572, d373254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35386 q selected
  have h17 (q : Pattern) (selected : d371573 q = 0) : d373255 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d371573, d373255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371573, d373255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d371574 q = 0) : d373256 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d371574, d373256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d371574, d373256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d371575 q = 0) : d373257 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d371575, d373257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371575, d373257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d371577 q = 0) : d373259 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d371577, d373259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38953 q selected
    | true =>
      simp only [d371577, d373259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35388 q selected
  have h21 (q : Pattern) (selected : d371578 q = 0) : d373260 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d371578, d373260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371578, d373260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d371579 q = 0) : d373261 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d371579, d373261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d371579, d373261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d371581 q = 0) : d373263 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d371581, d373263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38954 q selected
    | true =>
      simp only [d371581, d373263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38934 q selected
  have h24 (q : Pattern) (selected : d371583 q = 0) : d373170 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d371583, d373170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38955 q selected
    | true =>
      simp only [d371583, d373170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35391 q selected
  have h25 (q : Pattern) (selected : d371584 q = 0) : d373264 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d371584, d373264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d371584, d373264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d371586 q = 0) : d373266 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d371586, d373266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38956 q selected
    | true =>
      simp only [d371586, d373266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d371587 q = 0) : d373267 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d371587, d373267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d371587, d373267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d371588 q = 0) : d373268 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d371588, d373268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d371588, d373268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d371589 q = 0) : d373269 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d371589, d373269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d371589, d373269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d371590 q = 0) : d373270 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d371590, d373270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d371590, d373270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d371591 q = 0) : d373271 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d371591, d373271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d371591, d373271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro38958 (p : Pattern) (selected : d371593 p = 0) : d373273 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d371451 q = 0) : d373161 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d371451, d373161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38932 q selected
    | true =>
      simp only [d371451, d373161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35355 q selected
  have h2 (q : Pattern) (selected : d371452 q = 0) : d373162 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d371452, d373162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371452, d373162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d371453 q = 0) : d373163 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d371453, d373163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d371453, d373163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d371454 q = 0) : d373164 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d371454, d373164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371454, d373164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d371455 q = 0) : d373165 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d371455, d373165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371455, d373165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d339554 q = 0) : d341611 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d339554, d341611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35355 q selected
    | true =>
      simp only [d339554, d341611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d339555 q = 0) : d341612 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d339555, d341612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d339555, d341612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d339556 q = 0) : d341613 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d339556, d341613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d339556, d341613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d339557 q = 0) : d341614 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d339557, d341614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d339557, d341614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d339558 q = 0) : d341615 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d339558, d341615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d339558, d341615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d371593 q = 0) : d373273 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d371593, d373273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d371593, d373273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro38959 (p : Pattern) (selected : d371600 p = 0) : d373280 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d371581 q = 0) : d373263 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d371581, d373263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38954 q selected
    | true =>
      simp only [d371581, d373263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38934 q selected
  have h2 (q : Pattern) (selected : d371583 q = 0) : d373170 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d371583, d373170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38955 q selected
    | true =>
      simp only [d371583, d373170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35391 q selected
  have h3 (q : Pattern) (selected : d371584 q = 0) : d373264 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d371584, d373264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d371584, d373264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d371586 q = 0) : d373266 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d371586, d373266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38956 q selected
    | true =>
      simp only [d371586, d373266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d371587 q = 0) : d373267 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d371587, d373267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d371587, d373267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d371588 q = 0) : d373268 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d371588, d373268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d371588, d373268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d371598 q = 0) : d373278 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d371598, d373278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371598, d373278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d371599 q = 0) : d373279 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d371599, d373279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371599, d373279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d371600 q = 0) : d373280 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d371600, d373280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371600, d373280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro38960 (p : Pattern) (selected : d371620 p = 0) : d373300 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d371606 q = 0) : d373286 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d371606, d373286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371606, d373286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38939 q selected
  have h2 (q : Pattern) (selected : d371492 q = 0) : d373202 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d371492, d373202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38939 q selected
    | true =>
      simp only [d371492, d373202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d371607 q = 0) : d373287 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d371607, d373287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d371607, d373287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d371493 q = 0) : d373203 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d371493, d373203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d371493, d373203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d371608 q = 0) : d373288 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d371608, d373288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d371608, d373288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d371609 q = 0) : d373289 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d371609, d373289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d371609, d373289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d371610 q = 0) : d373290 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d371610, d373290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371610, d373290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38940 q selected
  have h8 (q : Pattern) (selected : d371501 q = 0) : d373211 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d371501, d373211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38940 q selected
    | true =>
      simp only [d371501, d373211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d371611 q = 0) : d373291 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d371611, d373291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d371611, d373291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d371502 q = 0) : d373212 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d371502, d373212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d371502, d373212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d371612 q = 0) : d373292 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d371612, d373292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d371612, d373292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d371613 q = 0) : d373293 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d371613, d373293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d371613, d373293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d371614 q = 0) : d373294 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d371614, d373294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d371614, d373294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d371615 q = 0) : d373295 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d371615, d373295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371615, d373295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38941 q selected
  have h15 (q : Pattern) (selected : d371510 q = 0) : d373220 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d371510, d373220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38941 q selected
    | true =>
      simp only [d371510, d373220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d371616 q = 0) : d373296 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d371616, d373296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d371616, d373296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d371511 q = 0) : d373221 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d371511, d373221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d371511, d373221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d371617 q = 0) : d373297 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d371617, d373297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d371617, d373297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d371618 q = 0) : d373298 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d371618, d373298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d371618, d373298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d339291 q = 0) : d341419 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d339291, d341419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d339291, d341419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35321 q selected
  have h21 (q : Pattern) (selected : d339191 q = 0) : d341349 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d339191, d341349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35321 q selected
    | true =>
      simp only [d339191, d341349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d339292 q = 0) : d341420 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d339292, d341420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d339292, d341420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d339192 q = 0) : d341350 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d339192, d341350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d339192, d341350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h24 (q : Pattern) (selected : d339293 q = 0) : d341421 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d339293, d341421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d339293, d341421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
  have h25 (q : Pattern) (selected : d339294 q = 0) : d341422 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d339294, d341422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
    | true =>
      simp only [d339294, d341422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h26 (q : Pattern) (selected : d371619 q = 0) : d373299 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d371619, d373299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d371619, d373299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d371620 q = 0) : d373300 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d371620, d373300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d371620, d373300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
theorem eqIntro38961 (p : Pattern) (selected : d371629 p = 0) : d373309 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d371621 q = 0) : d373301 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d371621, d373301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38960 q selected
    | true =>
      simp only [d371621, d373301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38925 q selected
  have h2 (q : Pattern) (selected : d371622 q = 0) : d373302 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d371622, d373302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371622, d373302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d371623 q = 0) : d373303 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d371623, d373303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371623, d373303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d371624 q = 0) : d373304 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d371624, d373304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38925 q selected
    | true =>
      simp only [d371624, d373304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35399 q selected
  have h5 (q : Pattern) (selected : d371625 q = 0) : d373305 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d371625, d373305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371625, d373305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d371626 q = 0) : d373306 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d371626, d373306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371626, d373306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d371627 q = 0) : d373307 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d371627, d373307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d371627, d373307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d371412 q = 0) : d373122 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d371412, d373122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38925 q selected
    | true =>
      simp only [d371412, d373122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35305 q selected
  have h9 (q : Pattern) (selected : d371413 q = 0) : d373123 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d371413, d373123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371413, d373123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d371414 q = 0) : d373124 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d371414, d373124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371414, d373124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d339094 q = 0) : d341271 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d339094, d341271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35305 q selected
    | true =>
      simp only [d339094, d341271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35278 q selected
  have h12 (q : Pattern) (selected : d339095 q = 0) : d341272 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d339095, d341272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d339095, d341272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d339096 q = 0) : d341273 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d339096, d341273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d339096, d341273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d371415 q = 0) : d373125 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d371415, d373125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d371415, d373125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d371628 q = 0) : d373308 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d371628, d373308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d371628, d373308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d371629 q = 0) : d373309 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d371629, d373309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d371629, d373309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro38962 (p : Pattern) (selected : d371633 p = 0) : d373313 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d371412 q = 0) : d373122 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d371412, d373122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38925 q selected
    | true =>
      simp only [d371412, d373122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35305 q selected
  have h2 (q : Pattern) (selected : d371413 q = 0) : d373123 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d371413, d373123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371413, d373123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d371414 q = 0) : d373124 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d371414, d373124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371414, d373124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d339094 q = 0) : d341271 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d339094, d341271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35305 q selected
    | true =>
      simp only [d339094, d341271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35278 q selected
  have h5 (q : Pattern) (selected : d339095 q = 0) : d341272 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d339095, d341272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d339095, d341272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d339096 q = 0) : d341273 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d339096, d341273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d339096, d341273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d371415 q = 0) : d373125 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d371415, d373125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d371415, d373125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d339607 q = 0) : d341664 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d339607, d341664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d339607, d341664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d371632 q = 0) : d373312 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d371632, d373312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d371632, d373312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d371633 q = 0) : d373313 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d371633, d373313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d371633, d373313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro38963 (p : Pattern) (selected : d371639 p = 0) : d373319 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d371630 q = 0) : d373310 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d371630, d373310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38961 q selected
    | true =>
      simp only [d371630, d373310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d371631 q = 0) : d373311 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d371631, d373311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371631, d373311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d371634 q = 0) : d373314 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d371634, d373314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38962 q selected
    | true =>
      simp only [d371634, d373314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d371635 q = 0) : d373315 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d371635, d373315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371635, d373315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d371636 q = 0) : d373316 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d371636, d373316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d371636, d373316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d371637 q = 0) : d373317 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d371637, d373317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d371637, d373317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d371638 q = 0) : d373318 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d371638, d373318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d371638, d373318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d371639 q = 0) : d373319 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d371639, d373319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d371639, d373319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro38964 (p : Pattern) (selected : d371643 p = 0) : d373323 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d371634 q = 0) : d373314 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d371634, d373314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38962 q selected
    | true =>
      simp only [d371634, d373314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d371635 q = 0) : d373315 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d371635, d373315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371635, d373315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d339618 q = 0) : d341675 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d339618, d341675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35403 q selected
    | true =>
      simp only [d339618, d341675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d339619 q = 0) : d341676 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d339619, d341676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d339619, d341676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d371640 q = 0) : d373320 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d371640, d373320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d371640, d373320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d371641 q = 0) : d373321 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d371641, d373321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d371641, d373321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d371642 q = 0) : d373322 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d371642, d373322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d371642, d373322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d371643 q = 0) : d373323 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d371643, d373323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d371643, d373323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro38965 (p : Pattern) (selected : d371650 p = 0) : d373121 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d371645 q = 0) : d373116 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d371645, d373116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371645, d373116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38946 q selected
  have h2 (q : Pattern) (selected : d371541 q = 0) : d373073 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d371541, d373073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38946 q selected
    | true =>
      simp only [d371541, d373073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d371646 q = 0) : d373117 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d371646, d373117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d371646, d373117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d371542 q = 0) : d373074 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d371542, d373074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d371542, d373074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d371647 q = 0) : d373118 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d371647, d373118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d371647, d373118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d371648 q = 0) : d373119 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d371648, d373119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d371648, d373119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d339310 q = 0) : d341265 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d339310, d341265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d339310, d341265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35326 q selected
  have h8 (q : Pattern) (selected : d339219 q = 0) : d341211 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d339219, d341211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35326 q selected
    | true =>
      simp only [d339219, d341211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d339311 q = 0) : d341266 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d339311, d341266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d339311, d341266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d339220 q = 0) : d341212 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d339220, d341212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d339220, d341212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d339312 q = 0) : d341267 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d339312, d341267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d339312, d341267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d339313 q = 0) : d341268 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d339313, d341268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d339313, d341268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d371649 q = 0) : d373120 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d371649, d373120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d371649, d373120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d339630 q = 0) : d341419 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d339630, d341419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d339630, d341419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35377 q selected
  have h15 (q : Pattern) (selected : d339490 q = 0) : d341349 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d339490, d341349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35377 q selected
    | true =>
      simp only [d339490, d341349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d339631 q = 0) : d341420 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d339631, d341420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d339631, d341420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d339491 q = 0) : d341350 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d339491, d341350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d339491, d341350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d339632 q = 0) : d341421 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d339632, d341421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d339632, d341421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d339633 q = 0) : d341422 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d339633, d341422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d339633, d341422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d339107 q = 0) : d341140 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d339107, d341140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d339107, d341140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35293 q selected
  have h21 (q : Pattern) (selected : d339032 q = 0) : d341099 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d339032, d341099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35293 q selected
    | true =>
      simp only [d339032, d341099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d339108 q = 0) : d341141 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d339108, d341141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d339108, d341141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d339033 q = 0) : d341100 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d339033, d341100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d339033, d341100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h24 (q : Pattern) (selected : d339109 q = 0) : d341142 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d339109, d341142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d339109, d341142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
  have h25 (q : Pattern) (selected : d339110 q = 0) : d341143 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d339110, d341143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
    | true =>
      simp only [d339110, d341143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h26 (q : Pattern) (selected : d339634 q = 0) : d341423 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d339634, d341423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d339634, d341423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d371650 q = 0) : d373121 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d371650, d373121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d371650, d373121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
theorem eqIntro38966 (p : Pattern) (selected : d371656 p = 0) : d373313 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d371651 q = 0) : d373122 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d371651, d373122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38965 q selected
    | true =>
      simp only [d371651, d373122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35344 q selected
  have h2 (q : Pattern) (selected : d371652 q = 0) : d373123 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d371652, d373123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371652, d373123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d371653 q = 0) : d373124 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d371653, d373124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371653, d373124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d339316 q = 0) : d341271 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d339316, d341271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35344 q selected
    | true =>
      simp only [d339316, d341271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35308 q selected
  have h5 (q : Pattern) (selected : d339317 q = 0) : d341272 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d339317, d341272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d339317, d341272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d339318 q = 0) : d341273 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d339318, d341273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d339318, d341273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d371654 q = 0) : d373125 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d371654, d373125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d371654, d373125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d339640 q = 0) : d341664 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d339640, d341664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d339640, d341664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d371655 q = 0) : d373312 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d371655, d373312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d371655, d373312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d371656 q = 0) : d373313 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d371656, d373313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d371656, d373313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro38967 (p : Pattern) (selected : d371662 p = 0) : d373323 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d371657 q = 0) : d373314 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d371657, d373314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38966 q selected
    | true =>
      simp only [d371657, d373314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d371658 q = 0) : d373315 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d371658, d373315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371658, d373315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d339647 q = 0) : d341675 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d339647, d341675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35407 q selected
    | true =>
      simp only [d339647, d341675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d339648 q = 0) : d341676 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d339648, d341676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d339648, d341676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d371659 q = 0) : d373320 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d371659, d373320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d371659, d373320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d371660 q = 0) : d373321 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d371660, d373321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d371660, d373321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d371661 q = 0) : d373322 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d371661, d373322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d371661, d373322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d371662 q = 0) : d373323 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d371662, d373323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d371662, d373323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro38968 (p : Pattern) (selected : d371668 p = 0) : d373330 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d371634 q = 0) : d373314 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d371634, d373314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38962 q selected
    | true =>
      simp only [d371634, d373314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d371635 q = 0) : d373315 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d371635, d373315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371635, d373315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d371665 q = 0) : d373327 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d371665, d373327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d371665, d373327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d371666 q = 0) : d373328 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d371666, d373328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d371666, d373328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d371667 q = 0) : d373329 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d371667, d373329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d371667, d373329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d371668 q = 0) : d373330 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d371668, d373330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d371668, d373330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38969 (p : Pattern) (selected : d371674 p = 0) : d373336 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d371644 q = 0) : d373324 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d371644, d373324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38963 q selected
    | true =>
      simp only [d371644, d373324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38964 q selected
  have h2 (q : Pattern) (selected : d371663 q = 0) : d373325 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d371663, d373325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38967 q selected
    | true =>
      simp only [d371663, d373325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35409 q selected
  have h3 (q : Pattern) (selected : d371664 q = 0) : d373326 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d371664, d373326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d371664, d373326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d371669 q = 0) : d373331 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d371669, d373331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38968 q selected
    | true =>
      simp only [d371669, d373331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d371670 q = 0) : d373332 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d371670, d373332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d371670, d373332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d371671 q = 0) : d373333 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d371671, d373333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d371671, d373333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d371672 q = 0) : d373334 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d371672, d373334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371672, d373334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d371673 q = 0) : d373335 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d371673, d373335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371673, d373335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d371674 q = 0) : d373336 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d371674, d373336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371674, d373336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro38970 (p : Pattern) (selected : d371680 p = 0) : d373342 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d371457 q = 0) : d373167 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d371457, d373167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371457, d373167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38933 q selected
  have h2 (q : Pattern) (selected : d371458 q = 0) : d373168 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d371458, d373168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d371458, d373168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d371466 q = 0) : d373176 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d371466, d373176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38933 q selected
    | true =>
      simp only [d371466, d373176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38935 q selected
  have h4 (q : Pattern) (selected : d371467 q = 0) : d373177 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d371467, d373177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d371467, d373177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d371468 q = 0) : d373178 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d371468, d373178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d371468, d373178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d371592 q = 0) : d373272 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d371592, d373272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38951 q selected
    | true =>
      simp only [d371592, d373272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38957 q selected
  have h7 (q : Pattern) (selected : d371594 q = 0) : d373274 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d371594, d373274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38958 q selected
    | true =>
      simp only [d371594, d373274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35395 q selected
  have h8 (q : Pattern) (selected : d371595 q = 0) : d373275 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d371595, d373275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d371595, d373275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d371596 q = 0) : d373276 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d371596, d373276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d371596, d373276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d371597 q = 0) : d373277 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d371597, d373277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d371597, d373277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d371601 q = 0) : d373281 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d371601, d373281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371601, d373281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38959 q selected
  have h12 (q : Pattern) (selected : d339575 q = 0) : d341632 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d339575, d341632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d339575, d341632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35397 q selected
  have h13 (q : Pattern) (selected : d371602 q = 0) : d373282 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d371602, d373282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d371602, d373282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d371603 q = 0) : d373283 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d371603, d373283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d371603, d373283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d371604 q = 0) : d373284 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d371604, d373284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d371604, d373284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d371605 q = 0) : d373285 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d371605, d373285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d371605, d373285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d371675 q = 0) : d373337 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d371675, d373337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371675, d373337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38969 q selected
  have h18 (q : Pattern) (selected : d339680 q = 0) : d341705 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d339680, d341705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d339680, d341705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35413 q selected
  have h19 (q : Pattern) (selected : d371676 q = 0) : d373338 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d371676, d373338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d371676, d373338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d371677 q = 0) : d373339 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d371677, d373339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d371677, d373339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d371678 q = 0) : d373340 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d371678, d373340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d371678, d373340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d371679 q = 0) : d373341 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d371679, d373341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d371679, d373341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d371680 q = 0) : d373342 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d371680, d373342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d371680, d373342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro38971 (p : Pattern) (selected : d371686 p = 0) : d373348 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d371681 q = 0) : d373343 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d371681, d373343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371681, d373343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38970 q selected
  have h2 (q : Pattern) (selected : d371682 q = 0) : d373344 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d371682, d373344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371682, d373344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d371683 q = 0) : d373345 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d371683, d373345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371683, d373345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d371684 q = 0) : d373346 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d371684, d373346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371684, d373346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d371685 q = 0) : d373347 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d371685, d373347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371685, d373347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d371686 q = 0) : d373348 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d371686, d373348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371686, d373348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro38972 (p : Pattern) (selected : d371689 p = 0) : d373351 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1 q = 0) : d0 q = 1 := by
    change (1 : Int) = 0 at selected
    omega
  have h2 (q : Pattern) (selected : d13 q = 0) : d127 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d325306 q = 0) : d341090 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d325306, d341090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d325306, d341090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d338884 q = 0) : d341091 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d338884, d341091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d338884, d341091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d371689 q = 0) : d373351 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d371689, d373351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371689, d373351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro38973 (p : Pattern) (selected : d371700 p = 0) : d373362 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d371690 q = 0) : d373352 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d371690, d373352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38916 q selected
    | true =>
      simp only [d371690, d373352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38972 q selected
  have h2 (q : Pattern) (selected : d371691 q = 0) : d373353 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d371691, d373353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d371691, d373353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d371692 q = 0) : d373354 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d371692, d373354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371692, d373354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d371357 q = 0) : d373067 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d371357, d373067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38916 q selected
    | true =>
      simp only [d371357, d373067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d371358 q = 0) : d373068 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d371358, d373068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d371358, d373068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d371483 q = 0) : d373193 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d371483, d373193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38938 q selected
    | true =>
      simp only [d371483, d373193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d371484 q = 0) : d373194 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d371484, d373194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d371484, d373194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d371485 q = 0) : d373195 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d371485, d373195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d371485, d373195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d371693 q = 0) : d373355 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d371693, d373355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d371693, d373355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d371694 q = 0) : d373356 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d371694, d373356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d371694, d373356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d371695 q = 0) : d373357 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d371695, d373357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35287 q selected
    | true =>
      simp only [d371695, d373357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35269 q selected
  have h12 (q : Pattern) (selected : d371696 q = 0) : d373358 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d371696, d373358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d371696, d373358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d371697 q = 0) : d373359 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d371697, d373359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d371697, d373359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d338886 q = 0) : d341093 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d338886, d341093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35269 q selected
    | true =>
      simp only [d338886, d341093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d338887 q = 0) : d341094 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d338887, d341094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d338887, d341094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d371488 q = 0) : d373198 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d371488, d373198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d371488, d373198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d371698 q = 0) : d373360 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d371698, d373360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d371698, d373360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d371699 q = 0) : d373361 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d371699, d373361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d371699, d373361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d371700 q = 0) : d373362 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d371700, d373362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d371700, d373362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro38974 (p : Pattern) (selected : d371712 p = 0) : d373374 p = 1 := by
  have h0 (q : Pattern) (selected : d371690 q = 0) : d373352 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d371690, d373352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38916 q selected
    | true =>
      simp only [d371690, d373352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38972 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d371691 q = 0) : d373353 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d371691, d373353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371691, d373353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d371695 q = 0) : d373357 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d371695, d373357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35287 q selected
    | true =>
      simp only [d371695, d373357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35269 q selected
  have h4 (q : Pattern) (selected : d371696 q = 0) : d373358 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d371696, d373358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d371696, d373358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d371697 q = 0) : d373359 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d371697, d373359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d371697, d373359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d338998 q = 0) : d341205 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d338998, d341205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35287 q selected
    | true =>
      simp only [d338998, d341205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h7 (q : Pattern) (selected : d338999 q = 0) : d341206 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d338999, d341206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d338999, d341206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d338886 q = 0) : d341093 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d338886, d341093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35269 q selected
    | true =>
      simp only [d338886, d341093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h9 (q : Pattern) (selected : d338887 q = 0) : d341094 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d338887, d341094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d338887, d341094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h10 (q : Pattern) (selected : d339000 q = 0) : d341207 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d339000, d341207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d339000, d341207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d371705 q = 0) : d373367 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d371705, d373367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d371705, d373367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d371706 q = 0) : d373368 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d371706, d373368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d371706, d373368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h13 (q : Pattern) (selected : d371707 q = 0) : d373369 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d371707, d373369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35573 q selected
    | true =>
      simp only [d371707, d373369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35269 q selected
  have h14 (q : Pattern) (selected : d371708 q = 0) : d373370 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d371708, d373370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d371708, d373370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h15 (q : Pattern) (selected : d371709 q = 0) : d373371 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d371709, d373371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d371709, d373371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h16 (q : Pattern) (selected : d371710 q = 0) : d373372 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d371710, d373372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d371710, d373372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h17 (q : Pattern) (selected : d371711 q = 0) : d373373 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d371711, d373373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d371711, d373373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h18 (q : Pattern) (selected : d371712 q = 0) : d373374 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d371712, d373374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d371712, d373374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro38975 (p : Pattern) (selected : d371721 p = 0) : d373383 p = 1 := by
  have h0 (q : Pattern) (selected : d371690 q = 0) : d373352 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d371690, d373352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38916 q selected
    | true =>
      simp only [d371690, d373352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38972 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d371691 q = 0) : d373353 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d371691, d373353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371691, d373353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d340557 q = 0) : d342321 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d340557, d342321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35573 q selected
    | true =>
      simp only [d340557, d342321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d371496 q = 0) : d373206 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d371496, d373206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d371496, d373206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d371718 q = 0) : d373380 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d371718, d373380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d371718, d373380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d371719 q = 0) : d373381 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d371719, d373381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d371719, d373381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h7 (q : Pattern) (selected : d371720 q = 0) : d373382 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d371720, d373382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d371720, d373382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d371707 q = 0) : d373369 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d371707, d373369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35573 q selected
    | true =>
      simp only [d371707, d373369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35269 q selected
  have h9 (q : Pattern) (selected : d371708 q = 0) : d373370 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d371708, d373370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d371708, d373370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h10 (q : Pattern) (selected : d338886 q = 0) : d341093 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d338886, d341093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35269 q selected
    | true =>
      simp only [d338886, d341093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h11 (q : Pattern) (selected : d338887 q = 0) : d341094 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d338887, d341094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d338887, d341094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h12 (q : Pattern) (selected : d371709 q = 0) : d373371 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d371709, d373371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d371709, d373371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d371710 q = 0) : d373372 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d371710, d373372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d371710, d373372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h14 (q : Pattern) (selected : d371711 q = 0) : d373373 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d371711, d373373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d371711, d373373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h15 (q : Pattern) (selected : d371721 q = 0) : d373383 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d371721, d373383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d371721, d373383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro38976 (p : Pattern) (selected : d371729 p = 0) : d373391 p = 1 := by
  have h0 (q : Pattern) (selected : d371695 q = 0) : d373357 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d371695, d373357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35287 q selected
    | true =>
      simp only [d371695, d373357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35269 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d371696 q = 0) : d373358 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d371696, d373358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371696, d373358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d338886 q = 0) : d341093 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d338886, d341093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35269 q selected
    | true =>
      simp only [d338886, d341093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d338887 q = 0) : d341094 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d338887, d341094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d338887, d341094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d371726 q = 0) : d373388 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d371726, d373388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d371726, d373388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d338888 q = 0) : d341095 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d338888, d341095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d338888, d341095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h7 (q : Pattern) (selected : d371727 q = 0) : d373389 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d371727, d373389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d371727, d373389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d371728 q = 0) : d373390 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d371728, d373390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d371728, d373390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h9 (q : Pattern) (selected : d371729 q = 0) : d373391 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d371729, d373391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d371729, d373391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h9 p selected
theorem eqIntro38977 (p : Pattern) (selected : d371735 p = 0) : d373397 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d371701 q = 0) : d373363 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d371701, d373363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38973 q selected
    | true =>
      simp only [d371701, d373363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d371702 q = 0) : d373364 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d371702, d373364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d371702, d373364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d371703 q = 0) : d373365 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d371703, d373365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371703, d373365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d371704 q = 0) : d373366 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d371704, d373366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d371704, d373366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d371713 q = 0) : d373375 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d371713, d373375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38974 q selected
    | true =>
      simp only [d371713, d373375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d371714 q = 0) : d373376 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d371714, d373376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d371714, d373376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d371715 q = 0) : d373377 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d371715, d373377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371715, d373377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d371716 q = 0) : d373378 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d371716, d373378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d371716, d373378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d371717 q = 0) : d373379 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d371717, d373379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d371717, d373379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d371722 q = 0) : d373384 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d371722, d373384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38975 q selected
    | true =>
      simp only [d371722, d373384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d371723 q = 0) : d373385 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d371723, d373385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d371723, d373385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d371724 q = 0) : d373386 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d371724, d373386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371724, d373386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d371725 q = 0) : d373387 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d371725, d373387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d371725, d373387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d371730 q = 0) : d373392 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d371730, d373392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38976 q selected
    | true =>
      simp only [d371730, d373392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d371731 q = 0) : d373393 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d371731, d373393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d371731, d373393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d371732 q = 0) : d373394 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d371732, d373394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371732, d373394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d371733 q = 0) : d373395 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d371733, d373395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d371733, d373395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d371734 q = 0) : d373396 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d371734, d373396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d371734, d373396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d371735 q = 0) : d373397 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d371735, d373397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d371735, d373397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro38978 (p : Pattern) (selected : d371736 p = 0) : d373398 p = 1 := by
  have h0 (q : Pattern) (selected : d371690 q = 0) : d373352 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d371690, d373352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38916 q selected
    | true =>
      simp only [d371690, d373352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38972 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d371691 q = 0) : d373353 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d371691, d373353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371691, d373353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d371695 q = 0) : d373357 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d371695, d373357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35287 q selected
    | true =>
      simp only [d371695, d373357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35269 q selected
  have h4 (q : Pattern) (selected : d371696 q = 0) : d373358 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d371696, d373358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d371696, d373358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d371697 q = 0) : d373359 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d371697, d373359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d371697, d373359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d338998 q = 0) : d341205 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d338998, d341205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35287 q selected
    | true =>
      simp only [d338998, d341205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h7 (q : Pattern) (selected : d338999 q = 0) : d341206 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d338999, d341206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d338999, d341206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d338886 q = 0) : d341093 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d338886, d341093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35269 q selected
    | true =>
      simp only [d338886, d341093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h9 (q : Pattern) (selected : d338887 q = 0) : d341094 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d338887, d341094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d338887, d341094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h10 (q : Pattern) (selected : d339000 q = 0) : d341207 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d339000, d341207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d339000, d341207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d371705 q = 0) : d373367 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d371705, d373367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d371705, d373367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d371706 q = 0) : d373368 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d371706, d373368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d371706, d373368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h13 (q : Pattern) (selected : d371726 q = 0) : d373388 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d371726, d373388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d371726, d373388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h14 (q : Pattern) (selected : d338888 q = 0) : d341095 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d338888, d341095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d338888, d341095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h15 (q : Pattern) (selected : d371727 q = 0) : d373389 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d371727, d373389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d371727, d373389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d371728 q = 0) : d373390 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d371728, d373390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d371728, d373390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h17 (q : Pattern) (selected : d371736 q = 0) : d373398 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d371736, d373398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d371736, d373398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro38979 (p : Pattern) (selected : d371743 p = 0) : d373405 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d371737 q = 0) : d373399 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d371737, d373399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38978 q selected
    | true =>
      simp only [d371737, d373399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d371738 q = 0) : d373400 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d371738, d373400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d371738, d373400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d371739 q = 0) : d373401 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d371739, d373401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371739, d373401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d371740 q = 0) : d373402 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d371740, d373402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d371740, d373402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d371730 q = 0) : d373392 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d371730, d373392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38976 q selected
    | true =>
      simp only [d371730, d373392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d371731 q = 0) : d373393 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d371731, d373393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d371731, d373393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d371732 q = 0) : d373394 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d371732, d373394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371732, d373394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d371733 q = 0) : d373395 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d371733, d373395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d371733, d373395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d371741 q = 0) : d373403 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d371741, d373403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d371741, d373403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d371742 q = 0) : d373404 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d371742, d373404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d371742, d373404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d371743 q = 0) : d373405 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d371743, d373405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d371743, d373405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro38980 (p : Pattern) (selected : d371747 p = 0) : d373409 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d371730 q = 0) : d373392 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d371730, d373392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38976 q selected
    | true =>
      simp only [d371730, d373392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d371731 q = 0) : d373393 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d371731, d373393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d371731, d373393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d371732 q = 0) : d373394 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d371732, d373394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371732, d373394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d371733 q = 0) : d373395 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d371733, d373395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d371733, d373395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d371742 q = 0) : d373404 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d371742, d373404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d371742, d373404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d371747 q = 0) : d373409 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d371747, d373409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d371747, d373409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38981 (p : Pattern) (selected : d371754 p = 0) : d373416 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d371744 q = 0) : d373406 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d371744, d373406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38977 q selected
    | true =>
      simp only [d371744, d373406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38979 q selected
  have h2 (q : Pattern) (selected : d371745 q = 0) : d373407 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d371745, d373407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371745, d373407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d371746 q = 0) : d373408 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d371746, d373408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371746, d373408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d371748 q = 0) : d373410 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d371748, d373410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38979 q selected
    | true =>
      simp only [d371748, d373410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38980 q selected
  have h5 (q : Pattern) (selected : d371749 q = 0) : d373411 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d371749, d373411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371749, d373411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d371750 q = 0) : d373412 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d371750, d373412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371750, d373412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d371751 q = 0) : d373413 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d371751, d373413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d371751, d373413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d371752 q = 0) : d373414 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d371752, d373414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d371752, d373414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d371753 q = 0) : d373415 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d371753, d373415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d371753, d373415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d371754 q = 0) : d373416 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d371754, d373416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d371754, d373416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro38982 (p : Pattern) (selected : d371758 p = 0) : d373420 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d371748 q = 0) : d373410 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d371748, d373410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38979 q selected
    | true =>
      simp only [d371748, d373410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38980 q selected
  have h2 (q : Pattern) (selected : d371749 q = 0) : d373411 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d371749, d373411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371749, d373411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d371750 q = 0) : d373412 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d371750, d373412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371750, d373412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d371752 q = 0) : d373414 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d371752, d373414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d371752, d373414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d371757 q = 0) : d373419 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d371757, d373419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d371757, d373419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d371758 q = 0) : d373420 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d371758, d373420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d371758, d373420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38983 (p : Pattern) (selected : d371764 p = 0) : d373426 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d371755 q = 0) : d373417 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d371755, d373417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38981 q selected
    | true =>
      simp only [d371755, d373417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d371756 q = 0) : d373418 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d371756, d373418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371756, d373418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d371759 q = 0) : d373421 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d371759, d373421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38982 q selected
    | true =>
      simp only [d371759, d373421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d371760 q = 0) : d373422 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d371760, d373422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371760, d373422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d371761 q = 0) : d373423 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d371761, d373423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d371761, d373423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d371762 q = 0) : d373424 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d371762, d373424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d371762, d373424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d371763 q = 0) : d373425 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d371763, d373425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d371763, d373425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d371764 q = 0) : d373426 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d371764, d373426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371764, d373426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro38984 (p : Pattern) (selected : d371768 p = 0) : d373430 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d371759 q = 0) : d373421 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d371759, d373421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38982 q selected
    | true =>
      simp only [d371759, d373421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d371760 q = 0) : d373422 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d371760, d373422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371760, d373422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d371765 q = 0) : d373427 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d371765, d373427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d371765, d373427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d371766 q = 0) : d373428 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d371766, d373428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d371766, d373428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d371767 q = 0) : d373429 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d371767, d373429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d371767, d373429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d371768 q = 0) : d373430 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d371768, d373430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371768, d373430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro38985 (p : Pattern) (selected : d371774 p = 0) : d373436 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d371769 q = 0) : d373431 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d371769, d373431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38983 q selected
    | true =>
      simp only [d371769, d373431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38984 q selected
  have h2 (q : Pattern) (selected : d371770 q = 0) : d373432 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d371770, d373432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371770, d373432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d371771 q = 0) : d373433 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d371771, d373433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d371771, d373433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d371772 q = 0) : d373434 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d371772, d373434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371772, d373434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d371773 q = 0) : d373435 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d371773, d373435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371773, d373435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d371774 q = 0) : d373436 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d371774, d373436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371774, d373436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro38986 (p : Pattern) (selected : d371777 p = 0) : d373439 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d371755 q = 0) : d373417 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d371755, d373417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38981 q selected
    | true =>
      simp only [d371755, d373417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d371756 q = 0) : d373418 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d371756, d373418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371756, d373418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d371759 q = 0) : d373421 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d371759, d373421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38982 q selected
    | true =>
      simp only [d371759, d373421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d371760 q = 0) : d373422 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d371760, d373422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371760, d373422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d371761 q = 0) : d373423 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d371761, d373423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d371761, d373423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d371762 q = 0) : d373424 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d371762, d373424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d371762, d373424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d371763 q = 0) : d373425 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d371763, d373425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d371763, d373425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d371777 q = 0) : d373439 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d371777, d373439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d371777, d373439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro38987 (p : Pattern) (selected : d371778 p = 0) : d373440 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d371759 q = 0) : d373421 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d371759, d373421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38982 q selected
    | true =>
      simp only [d371759, d373421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d371760 q = 0) : d373422 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d371760, d373422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371760, d373422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d371765 q = 0) : d373427 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d371765, d373427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d371765, d373427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d371766 q = 0) : d373428 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d371766, d373428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d371766, d373428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d371767 q = 0) : d373429 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d371767, d373429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d371767, d373429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d371778 q = 0) : d373440 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d371778, d373440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d371778, d373440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro38988 (p : Pattern) (selected : d371784 p = 0) : d373446 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d371769 q = 0) : d373431 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d371769, d373431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38983 q selected
    | true =>
      simp only [d371769, d373431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38984 q selected
  have h2 (q : Pattern) (selected : d371770 q = 0) : d373432 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d371770, d373432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371770, d373432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d371771 q = 0) : d373433 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d371771, d373433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d371771, d373433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d371772 q = 0) : d373434 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d371772, d373434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371772, d373434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d371773 q = 0) : d373435 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d371773, d373435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371773, d373435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d371779 q = 0) : d373441 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d371779, d373441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38986 q selected
    | true =>
      simp only [d371779, d373441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38987 q selected
  have h7 (q : Pattern) (selected : d371780 q = 0) : d373442 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d371780, d373442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371780, d373442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d371781 q = 0) : d373443 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d371781, d373443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d371781, d373443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d371782 q = 0) : d373444 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d371782, d373444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371782, d373444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d371783 q = 0) : d373445 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d371783, d373445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371783, d373445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d371784 q = 0) : d373446 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d371784, d373446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d371784, d373446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro38989 (p : Pattern) (selected : d371789 p = 0) : d373451 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d371755 q = 0) : d373417 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d371755, d373417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38981 q selected
    | true =>
      simp only [d371755, d373417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d371756 q = 0) : d373418 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d371756, d373418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371756, d373418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d371759 q = 0) : d373421 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d371759, d373421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38982 q selected
    | true =>
      simp only [d371759, d373421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d371760 q = 0) : d373422 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d371760, d373422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371760, d373422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d371761 q = 0) : d373423 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d371761, d373423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d371761, d373423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d371762 q = 0) : d373424 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d371762, d373424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d371762, d373424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d371788 q = 0) : d373450 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d371788, d373450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371788, d373450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d371789 q = 0) : d373451 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d371789, d373451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371789, d373451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro38990 (p : Pattern) (selected : d371791 p = 0) : d373453 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d371759 q = 0) : d373421 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d371759, d373421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38982 q selected
    | true =>
      simp only [d371759, d373421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d371760 q = 0) : d373422 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d371760, d373422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371760, d373422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d371765 q = 0) : d373427 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d371765, d373427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d371765, d373427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d371766 q = 0) : d373428 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d371766, d373428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d371766, d373428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d371790 q = 0) : d373452 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d371790, d373452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371790, d373452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d371791 q = 0) : d373453 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d371791, d373453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371791, d373453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro38991 (p : Pattern) (selected : d371798 p = 0) : d373460 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d371755 q = 0) : d373417 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d371755, d373417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38981 q selected
    | true =>
      simp only [d371755, d373417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d371756 q = 0) : d373418 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d371756, d373418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371756, d373418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d371759 q = 0) : d373421 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d371759, d373421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38982 q selected
    | true =>
      simp only [d371759, d373421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d371760 q = 0) : d373422 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d371760, d373422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371760, d373422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d371761 q = 0) : d373423 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d371761, d373423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d371761, d373423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d371796 q = 0) : d373458 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d371796, d373458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371796, d373458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d371797 q = 0) : d373459 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d371797, d373459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d371797, d373459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d371798 q = 0) : d373460 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d371798, d373460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371798, d373460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro38992 (p : Pattern) (selected : d371801 p = 0) : d373463 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d371759 q = 0) : d373421 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d371759, d373421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38982 q selected
    | true =>
      simp only [d371759, d373421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d371760 q = 0) : d373422 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d371760, d373422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371760, d373422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d371765 q = 0) : d373427 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d371765, d373427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d371765, d373427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d371799 q = 0) : d373461 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d371799, d373461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371799, d373461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d371800 q = 0) : d373462 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d371800, d373462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d371800, d373462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d371801 q = 0) : d373463 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d371801, d373463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371801, d373463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro38993 (p : Pattern) (selected : d371805 p = 0) : d373467 p = 1 := by
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
  have h3 (q : Pattern) (selected : d339417 q = 0) : d341526 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d339417, d341526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d339417, d341526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13 q = 0) : d127 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d325306 q = 0) : d341090 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d325306, d341090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d325306, d341090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d371355 q = 0) : d373065 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d371355, d373065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d371355, d373065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d371805 q = 0) : d373467 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d371805, d373467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371805, d373467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro38994 (p : Pattern) (selected : d371814 p = 0) : d373476 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d371806 q = 0) : d373468 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d371806, d373468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38993 q selected
    | true =>
      simp only [d371806, d373468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d371807 q = 0) : d373469 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d371807, d373469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d371807, d373469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d371808 q = 0) : d373470 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d371808, d373470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371808, d373470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d371809 q = 0) : d373471 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d371809, d373471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371809, d373471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d371810 q = 0) : d373472 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d371810, d373472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d371810, d373472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d371690 q = 0) : d373352 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d371690, d373352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38916 q selected
    | true =>
      simp only [d371690, d373352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38972 q selected
  have h7 (q : Pattern) (selected : d371691 q = 0) : d373353 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d371691, d373353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d371691, d373353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d371692 q = 0) : d373354 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d371692, d373354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371692, d373354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d371483 q = 0) : d373193 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d371483, d373193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38938 q selected
    | true =>
      simp only [d371483, d373193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d371484 q = 0) : d373194 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d371484, d373194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d371484, d373194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d371811 q = 0) : d373473 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d371811, d373473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d371811, d373473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d371812 q = 0) : d373474 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d371812, d373474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d371812, d373474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d371813 q = 0) : d373475 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d371813, d373475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d371813, d373475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d371814 q = 0) : d373476 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d371814, d373476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d371814, d373476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  exact h14 p selected
theorem eqIntro38995 (p : Pattern) (selected : d371819 p = 0) : d373481 p = 1 := by
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
  have h3 (q : Pattern) (selected : d339170 q = 0) : d341328 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d339170, d341328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d339170, d341328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d371354 q = 0) : d373064 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d371354, d373064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d371354, d373064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d371819 q = 0) : d373481 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d371819, d373481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d371819, d373481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro38996 (p : Pattern) (selected : d371825 p = 0) : d373487 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d371690 q = 0) : d373352 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d371690, d373352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38916 q selected
    | true =>
      simp only [d371690, d373352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38972 q selected
  have h2 (q : Pattern) (selected : d371691 q = 0) : d373353 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d371691, d373353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d371691, d373353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d371692 q = 0) : d373354 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d371692, d373354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371692, d373354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d371357 q = 0) : d373067 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d371357, d373067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38916 q selected
    | true =>
      simp only [d371357, d373067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d371358 q = 0) : d373068 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d371358, d373068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d371358, d373068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d371483 q = 0) : d373193 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d371483, d373193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38938 q selected
    | true =>
      simp only [d371483, d373193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d371484 q = 0) : d373194 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d371484, d373194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d371484, d373194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d371485 q = 0) : d373195 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d371485, d373195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d371485, d373195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d371693 q = 0) : d373355 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d371693, d373355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d371693, d373355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d371694 q = 0) : d373356 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d371694, d373356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d371694, d373356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d371820 q = 0) : d373482 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d371820, d373482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38995 q selected
    | true =>
      simp only [d371820, d373482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d371821 q = 0) : d373483 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d371821, d373483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d371821, d373483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d340557 q = 0) : d342321 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d340557, d342321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35573 q selected
    | true =>
      simp only [d340557, d342321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d371496 q = 0) : d373206 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d371496, d373206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d371496, d373206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d371822 q = 0) : d373484 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d371822, d373484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d371822, d373484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d371823 q = 0) : d373485 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d371823, d373485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d371823, d373485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d371824 q = 0) : d373486 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d371824, d373486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d371824, d373486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d371825 q = 0) : d373487 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d371825, d373487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d371825, d373487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro38997 (p : Pattern) (selected : d371834 p = 0) : d373496 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d371820 q = 0) : d373482 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d371820, d373482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38995 q selected
    | true =>
      simp only [d371820, d373482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d371821 q = 0) : d373483 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d371821, d373483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d371821, d373483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d371831 q = 0) : d373493 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d371831, d373493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371831, d373493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d371832 q = 0) : d373494 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d371832, d373494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d371832, d373494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d371833 q = 0) : d373495 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d371833, d373495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d371833, d373495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d340557 q = 0) : d342321 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d340557, d342321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35573 q selected
    | true =>
      simp only [d340557, d342321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d371496 q = 0) : d373206 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d371496, d373206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d371496, d373206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d371822 q = 0) : d373484 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d371822, d373484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d371822, d373484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d371823 q = 0) : d373485 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d371823, d373485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d371823, d373485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d371824 q = 0) : d373486 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d371824, d373486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d371824, d373486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d371834 q = 0) : d373496 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d371834, d373496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d371834, d373496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro38998 (p : Pattern) (selected : d371840 p = 0) : d373502 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d371815 q = 0) : d373477 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d371815, d373477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38994 q selected
    | true =>
      simp only [d371815, d373477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d371816 q = 0) : d373478 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d371816, d373478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d371816, d373478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d371817 q = 0) : d373479 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d371817, d373479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371817, d373479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d371818 q = 0) : d373480 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d371818, d373480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d371818, d373480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d371826 q = 0) : d373488 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d371826, d373488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38996 q selected
    | true =>
      simp only [d371826, d373488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d371827 q = 0) : d373489 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d371827, d373489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d371827, d373489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d371828 q = 0) : d373490 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d371828, d373490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371828, d373490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d371829 q = 0) : d373491 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d371829, d373491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d371829, d373491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d371830 q = 0) : d373492 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d371830, d373492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d371830, d373492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d371835 q = 0) : d373497 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d371835, d373497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38997 q selected
    | true =>
      simp only [d371835, d373497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d371836 q = 0) : d373498 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d371836, d373498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d371836, d373498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d371837 q = 0) : d373499 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d371837, d373499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371837, d373499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d371838 q = 0) : d373500 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d371838, d373500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d371838, d373500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d371722 q = 0) : d373384 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d371722, d373384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38975 q selected
    | true =>
      simp only [d371722, d373384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d371723 q = 0) : d373385 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d371723, d373385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d371723, d373385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d371724 q = 0) : d373386 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d371724, d373386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371724, d373386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d371725 q = 0) : d373387 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d371725, d373387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d371725, d373387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d371839 q = 0) : d373501 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d371839, d373501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d371839, d373501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d371840 q = 0) : d373502 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d371840, d373502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d371840, d373502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro38999 (p : Pattern) (selected : d371847 p = 0) : d373509 p = 1 := by
  have h0 (q : Pattern) (selected : d371690 q = 0) : d373352 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d371690, d373352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38916 q selected
    | true =>
      simp only [d371690, d373352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38972 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d371691 q = 0) : d373353 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d371691, d373353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d371691, d373353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d371707 q = 0) : d373369 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d371707, d373369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35573 q selected
    | true =>
      simp only [d371707, d373369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35269 q selected
  have h4 (q : Pattern) (selected : d371708 q = 0) : d373370 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d371708, d373370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d371708, d373370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d371844 q = 0) : d373506 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d371844, d373506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d371844, d373506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d371845 q = 0) : d373507 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d371845, d373507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d371845, d373507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h7 (q : Pattern) (selected : d371846 q = 0) : d373508 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d371846, d373508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d371846, d373508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d338886 q = 0) : d341093 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d338886, d341093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35269 q selected
    | true =>
      simp only [d338886, d341093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h9 (q : Pattern) (selected : d338887 q = 0) : d341094 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d338887, d341094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d338887, d341094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h10 (q : Pattern) (selected : d371709 q = 0) : d373371 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d371709, d373371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d371709, d373371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d371710 q = 0) : d373372 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d371710, d373372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d371710, d373372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h12 (q : Pattern) (selected : d371711 q = 0) : d373373 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d371711, d373373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d371711, d373373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h13 (q : Pattern) (selected : d371847 q = 0) : d373509 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d371847, d373509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d371847, d373509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
end NetHack.Soko22Hazard87
